import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V16_82

set_option maxSynthPendingDepth 3

/-! Round trip for V16_82 (2021 Theorem 16.6.6, p. 739, Fredholm index `0`; 2017: Theorem 16.8).

**Universes.**  Every universe-polymorphic theorem of the item is instantiated at `0` (`B` lives
in `Type`); the example theorems (`TrivialBundle`, `z3`, `OrbifoldSquare`) are monomorphic.
`A` is the conjunction of the types of the 81 theorems listed (the 15 definitions and structures
of the list are vocabulary).

**Main forms against `B`.**  `theorem_16_6_6_index_zero_wellDefined_unconditional` (and its parts
`..._solutionSet_noBumps`, `..._count_eq_unconditional`, `..._all_admissible_unconditional`) assume
`CanonicalGermInput o 0` = tame germ data of the model `F` of `o`
(`IsScFredholmSectionTame`) **and** index `0` at smooth objects.  `B` assumes only the index.
Every other main form of the list (`_wellDefined`, `_exists`, `_wellDefined_all`, `_count_eq`,
`_all_admissible_wellDefined`, `_canonical`, `_inherited`, ...) assumes `CanonicalInput`,
`CanonicalBumpInput`, `CanonicalInput_all` or `IndexZeroInput`, all of which carry tameness too.
Tameness is not implied by `∂Z = ∅` in the project (`UntamedCorner`, `TameGermTransfer.lean`: germ
data with `d_X = 0` in a chart with `d_C(0) = 1` need not be tame).  So `A → B` is not proved;
`A_to_B_tame` proves `B` with the tameness hypothesis added (the only gap).

**Harness note.**  `A`'s statement itself reaches the banned
`StrongBundleLocalizationExamples.pullOr_ofHom_z3InvHom`: it is a direct (non-abstracted) argument
of the definition `z3InvCorrespondence` in the type of the conjunct
`theorem_16_6_6_index_zero_correspondence_z3` (and `EP.isPointTame_sub`,
`EpFunctor.isPointTame_pullSection_of` through `_proof_` fields).  So every term mentioning `A`
fails `#rt_check` (recorded with `#guard_msgs`); the glue is therefore checked on
`main_to_B_tame`, which takes only the conjunct it uses and passes plain `#rt_check`.

Conversely `B` states the weighted count `∫_θ̂ τ` only, while every main form of `A` also states
the effective count `∮_θ̂ τ`; and `A` contains ~75 auxiliary ep-groupoid lemmas, alternative
forms and worked examples that `B` does not state.  `B_gives_main` derives from `B` the
existence part and the `∫` part of `theorem_16_6_6_index_zero_wellDefined_unconditional`
(with `HasCompactSolutionSet` added, which `B` assumes and the project form does not).

**Satisfiability.**  `CanonicalGermInput o 0` and `IsCanonicalPointSolutionSet o Q` are
satisfiable: `OrbifoldSquare.theorem_16_6_6_hypotheses`, `OrbifoldSquare.exists_canonical_t5`
(conjuncts of `A`). -/

namespace RoundTrip.V16_82
open Polyfold

/-- The project's statement: the conjunction of the item's 81 theorems (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible_unconditional.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_count_eq_unconditional.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined_unconditional.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_solutionSet_noBumps.{0}) ∧
  (type_of% @Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation_restr.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PointSolution.count_restr.{0}) ∧
  (type_of% @Polyfold.SBLocalization.PointSolution.countEff_restr.{0}) ∧
  (type_of% @Polyfold.EP.isPointTame_sub.{0}) ∧
  (type_of% @Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation_loc.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_1_cylinder_index_zero_loc.{0}) ∧
  (type_of% @Polyfold.EpFunctor.isPointTame_pullSection_of.{0}) ∧
  (type_of% @Polyfold.EpFunctor.pointIntegral_pull_of.{0}) ∧
  (type_of% @Polyfold.EpFunctor.pointIntegralEff_pull_of.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_signed_generator_cubeOrientation_loc.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_arePointMatchedAt_of_kernelCanonical_loc.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_indexZeroInput.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasOrientedCobordism_of_isCanonical.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented.{0}) ∧
  (type_of% @Polyfold.SBLocalization.theorem_15_4_1_cylinder_index_zero.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.indexZeroInput_of_canonicalInput.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical_input.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical_input.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_inherited.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_inherited.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_signed_generator_cubeOrientation.{0}) ∧
  (type_of% @Polyfold.SBLocalization.frameSign_boundaryOrient_of_generator.{0}) ∧
  (type_of% @Polyfold.SBLocalization.boundaryBranchedMeasureDim1_cylEnd_of_pointMatched.{0}) ∧
  (type_of% @Polyfold.TrivialBundle.equiv_negStructure_epStructure) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq_two_structures) ∧
  (type_of% @Polyfold.TrivialBundle.corollary_15_4_4_index_zero_hypotheses_twoPointSection) ∧
  (type_of% @Polyfold.TrivialBundle.exists_isCanonical_twoPointSection) ∧
  (type_of% @Polyfold.TrivialBundle.corollary_15_4_4_index_zero_twoPointSection) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.corollary_15_4_4_index_zero_hypotheses_z3) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.corollary_15_4_4_index_zero_z3) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.indexZeroInput_z3OrientationRep) ∧
  (type_of% @Polyfold.TrivialBundle.corollary_15_4_4_index_zero_two_perturbations) ∧
  (type_of% @Polyfold.PolyfoldClass.PointSuborbifold.count_eq_of_hasCobordism.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.PointSuborbifold.countEff_eq_of_hasCobordismEff.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_of_model.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_of_model_statement.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_hcob_witness.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_index_zero.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_of_model.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_hcob_witness.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq_two_models) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_iff_of_correspondence.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_generalPosition_iff_of_correspondence.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence_generalPosition.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.pointOrientedRep_rel_of_diagram.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_of_diagram.{0}) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.theorem_16_6_6_index_zero_correspondence_z3) ∧
  (type_of% @Polyfold.StrongBundleLocalizationExamples.pullOr_ofHom_z3InvHom) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_exists.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined.{0}) ∧
  (type_of% @Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.isTransversalPerturbation_of_isAdmissible_point.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_solutionSet_of_bump.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_count_eq.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible_wellDefined.{0}) ∧
  (type_of% @Polyfold.TrivialBundle.corollary_15_4_4_index_zero_norm_one) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_indexZeroInput_all.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical_all.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical_all.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_inherited_all.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_exists_all.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined_all.{0}) ∧
  (type_of% @Polyfold.PolyfoldClass.PointSuborbifold.count_eq_of_hasCobordism_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented_all.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence_all.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_iff_of_correspondence_all.{0}) ∧
  (type_of% @Polyfold.Examples.OrbifoldSquare.theorem_16_6_6_hypotheses) ∧
  (type_of% @Polyfold.Examples.OrbifoldSquare.theorem_16_6_6_sq) ∧
  (type_of% @Polyfold.Examples.OrbifoldSquare.not_isTransversalAt_sectionMulti) ∧
  (type_of% @Polyfold.Examples.OrbifoldSquare.exists_canonical_t5) ∧
  (type_of% @Polyfold.Examples.OrbifoldSquare.count_eq_two_fifths) ∧
  (type_of% @Polyfold.Examples.OrbifoldSquare.count_eq_two_fifths_all)

theorem A_holds : A :=
  ⟨@Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible_unconditional.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_count_eq_unconditional.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined_unconditional.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_solutionSet_noBumps.{0},
   @Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation_restr.{0},
   @Polyfold.SBLocalization.PointSolution.count_restr.{0},
   @Polyfold.SBLocalization.PointSolution.countEff_restr.{0},
   @Polyfold.EP.isPointTame_sub.{0},
   @Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation_loc.{0},
   @Polyfold.SBLocalization.theorem_15_4_1_cylinder_index_zero_loc.{0},
   @Polyfold.EpFunctor.isPointTame_pullSection_of.{0},
   @Polyfold.EpFunctor.pointIntegral_pull_of.{0},
   @Polyfold.EpFunctor.pointIntegralEff_pull_of.{0},
   @Polyfold.SBLocalization.exists_signed_generator_cubeOrientation_loc.{0},
   @Polyfold.SBLocalization.exists_arePointMatchedAt_of_kernelCanonical_loc.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical.{0},
   @Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_indexZeroInput.{0},
   @Polyfold.SBLocalization.hasOrientedCobordism_of_isCanonical.{0},
   @Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented.{0},
   @Polyfold.SBLocalization.theorem_15_4_1_cylinder_index_zero.{0},
   @Polyfold.StrongPolyfoldBundle.indexZeroInput_of_canonicalInput.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical_input.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical_input.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_inherited.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_inherited.{0},
   @Polyfold.SBLocalization.exists_signed_generator_cubeOrientation.{0},
   @Polyfold.SBLocalization.frameSign_boundaryOrient_of_generator.{0},
   @Polyfold.SBLocalization.boundaryBranchedMeasureDim1_cylEnd_of_pointMatched.{0},
   @Polyfold.TrivialBundle.equiv_negStructure_epStructure,
   @Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq_two_structures,
   @Polyfold.TrivialBundle.corollary_15_4_4_index_zero_hypotheses_twoPointSection,
   @Polyfold.TrivialBundle.exists_isCanonical_twoPointSection,
   @Polyfold.TrivialBundle.corollary_15_4_4_index_zero_twoPointSection,
   @Polyfold.StrongBundleLocalizationExamples.corollary_15_4_4_index_zero_hypotheses_z3,
   @Polyfold.StrongBundleLocalizationExamples.corollary_15_4_4_index_zero_z3,
   @Polyfold.StrongBundleLocalizationExamples.indexZeroInput_z3OrientationRep,
   @Polyfold.TrivialBundle.corollary_15_4_4_index_zero_two_perturbations,
   @Polyfold.PolyfoldClass.PointSuborbifold.count_eq_of_hasCobordism.{0},
   @Polyfold.PolyfoldClass.PointSuborbifold.countEff_eq_of_hasCobordismEff.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_of_model.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_of_model_statement.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_hcob_witness.{0},
   @Polyfold.SBLocalization.corollary_15_4_4_index_zero.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_of_model.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_hcob_witness.{0},
   @Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq.{0},
   @Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq_two_models,
   @Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_iff_of_correspondence.{0},
   @Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_generalPosition_iff_of_correspondence.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence_generalPosition.{0},
   @Polyfold.StrongPolyfoldBundle.pointOrientedRep_rel_of_diagram.{0},
   @Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_of_diagram.{0},
   @Polyfold.StrongBundleLocalizationExamples.theorem_16_6_6_index_zero_correspondence_z3,
   @Polyfold.StrongBundleLocalizationExamples.pullOr_ofHom_z3InvHom,
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_exists.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined.{0},
   @Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation.{0},
   @Polyfold.StrongPolyfoldBundle.isTransversalPerturbation_of_isAdmissible_point.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_solutionSet_of_bump.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_count_eq.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible_wellDefined.{0},
   @Polyfold.TrivialBundle.corollary_15_4_4_index_zero_norm_one,
   @Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_indexZeroInput_all.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical_all.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical_all.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_inherited_all.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_exists_all.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined_all.{0},
   @Polyfold.PolyfoldClass.PointSuborbifold.count_eq_of_hasCobordism_all.{0},
   @Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented_all.{0},
   @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence_all.{0},
   @Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_iff_of_correspondence_all.{0},
   @Polyfold.Examples.OrbifoldSquare.theorem_16_6_6_hypotheses,
   @Polyfold.Examples.OrbifoldSquare.theorem_16_6_6_sq,
   @Polyfold.Examples.OrbifoldSquare.not_isTransversalAt_sectionMulti,
   @Polyfold.Examples.OrbifoldSquare.exists_canonical_t5,
   @Polyfold.Examples.OrbifoldSquare.count_eq_two_fifths,
   @Polyfold.Examples.OrbifoldSquare.count_eq_two_fifths_all⟩


/-- `B` with tame germ data of the model of `o` added (the hypothesis every main form of `A`
carries in `CanonicalGermInput`). -/
def B_tame : Prop :=
  ∀ {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
    (c : StrongPolyfoldBundle p),
    c.polyfold.boundary = ∅ →
    ∀ (f : c.FredholmSection) (o : StrongPolyfoldBundle.OrientationRep f),
    (∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x 0) →
    o.a.S.A.B.IsScFredholmSectionTame o.a.F →
    (f : c.ScSection).HasCompactSolutionSet →
    ∀ (n : Y → ℝ) (U : Set Z),
    c.IsAuxNorm n → IsOpen U → (f : c.ScSection).solutionSet ⊆ U →
    (f : c.ScSection).ControlsCompactness n U →
      (∀ lam : c.ScPlusMultisection, Admissible f n U lam →
        ∃ Q : StrongPolyfoldBundle.PointOrientedPerturbation (f : c.ScSection),
          Q.t = lam ∧ StrongPolyfoldBundle.IsCanonicalPointSolutionSet o Q) ∧
      (∀ Q Q' : StrongPolyfoldBundle.PointOrientedPerturbation (f : c.ScSection),
        Admissible f n U Q.t → StrongPolyfoldBundle.IsCanonicalPointSolutionSet o Q →
        Admissible f n U Q'.t → StrongPolyfoldBundle.IsCanonicalPointSolutionSet o Q' →
        ∀ (τ : c.polyfold.ScForm 0), PolyfoldClass.ScForm.d τ = 0 →
          Q.toPointSuborbifold.count τ = Q'.toPointSuborbifold.count τ)

/-- `B` without tameness differs from `B_tame` by exactly that hypothesis. -/
theorem B_imp_B_tame : B → B_tame := by
  intro hB Y Z _ _ p c hbd f o hidx _ hcpt n U hn hU hsub hcc
  exact hB c hbd f o hidx hcpt n U hn hU hsub hcc

/-- **The main form gives `B` once tame germ data are added**: from
`theorem_16_6_6_index_zero_wellDefined_unconditional` (conjunct 3 of `A`). -/
theorem main_to_B_tame :
    (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined_unconditional.{0})
      → B_tame := by
  intro hW Y Z _ _ p c hbd f o hidx htame _ n U hn hU _ hcc
  have W := hW hbd hn hU hcc (o := o) ⟨htame, fun x hx => by exact_mod_cast hidx x hx⟩
  refine ⟨fun lam hadm => ?_, fun Q Q' a ca a' ca' τ hτ => (W.2 Q Q' a ca a' ca' τ hτ).1⟩
  obtain ⟨Q, hQt, -, hQc⟩ := W.1 lam hadm.1 hadm.2
  exact ⟨Q, hQt, hQc⟩

/-- **`A ⇒ B` once tame germ data are added.** -/
theorem A_to_B_tame : A → B_tame := fun hA => main_to_B_tame hA.2.2.1

/-- **What `B` gives of the main form**: the existence part and the `∫` part of
`theorem_16_6_6_index_zero_wellDefined_unconditional`, with `HasCompactSolutionSet` added (a
hypothesis of `B`, not of the project form).  The `∮` part is not in `B`. -/
theorem B_gives_main : B →
    ∀ {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
      {c : StrongPolyfoldBundle p}, c.polyfold.boundary = ∅ →
      ∀ {s : c.FredholmSection} {n : Y → ℝ}, c.IsAuxNorm n → ∀ {U : Set Z}, IsOpen U →
        (s : c.ScSection).ControlsCompactness n U → (s : c.ScSection).HasCompactSolutionSet →
        ∀ {o : StrongPolyfoldBundle.OrientationRep s}, StrongPolyfoldBundle.CanonicalGermInput o 0 →
        (∀ t : c.ScPlusMultisection, t.IsControlledBy n U →
            (s : c.ScSection).IsInGeneralPositionWith t →
            ∃ Q : StrongPolyfoldBundle.PointOrientedPerturbation (s : c.ScSection), Q.t = t ∧
              Q.IsAdmissible n U ∧ StrongPolyfoldBundle.IsCanonicalPointSolutionSet o Q) ∧
        ∀ Q₀ Q₁ : StrongPolyfoldBundle.PointOrientedPerturbation (s : c.ScSection),
          Q₀.IsAdmissible n U → StrongPolyfoldBundle.IsCanonicalPointSolutionSet o Q₀ →
          Q₁.IsAdmissible n U → StrongPolyfoldBundle.IsCanonicalPointSolutionSet o Q₁ →
          ∀ τ : c.polyfold.ScForm 0, PolyfoldClass.ScForm.d τ = 0 → Q₀.count τ = Q₁.count τ := by
  intro hB Y Z _ _ p c hbd s n hn U hU hcc hcpt o H
  obtain ⟨h1, h2⟩ := hB c hbd s o (fun x hx => by exact_mod_cast H.index x hx) hcpt n U hn hU
    hcc.2.2.1 hcc
  refine ⟨fun t ht hgp => ?_, fun Q₀ Q₁ a₀ c₀ a₁ c₁ τ hτ => h2 Q₀ Q₁ a₀ c₀ a₁ c₁ τ hτ⟩
  obtain ⟨Q, hQt, hQc⟩ := h1 t ⟨ht, hgp⟩
  refine ⟨Q, hQt, ?_, hQc⟩
  show Q.t.IsControlledBy n U ∧ _
  rw [hQt]; exact ⟨ht, hgp⟩

#rt_check RoundTrip.V16_82.main_to_B_tame [Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_count_eq_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_solutionSet_noBumps,
  Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation_restr,
  Polyfold.SBLocalization.PointSolution.count_restr,
  Polyfold.SBLocalization.PointSolution.countEff_restr,
  Polyfold.EP.isPointTame_sub,
  Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation_loc,
  Polyfold.SBLocalization.theorem_15_4_1_cylinder_index_zero_loc,
  Polyfold.EpFunctor.isPointTame_pullSection_of,
  Polyfold.EpFunctor.pointIntegral_pull_of,
  Polyfold.EpFunctor.pointIntegralEff_pull_of,
  Polyfold.SBLocalization.exists_signed_generator_cubeOrientation_loc,
  Polyfold.SBLocalization.exists_arePointMatchedAt_of_kernelCanonical_loc,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical,
  Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_indexZeroInput,
  Polyfold.SBLocalization.hasOrientedCobordism_of_isCanonical,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented,
  Polyfold.SBLocalization.theorem_15_4_1_cylinder_index_zero,
  Polyfold.StrongPolyfoldBundle.indexZeroInput_of_canonicalInput,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical_input,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical_input,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_inherited,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_inherited,
  Polyfold.SBLocalization.exists_signed_generator_cubeOrientation,
  Polyfold.SBLocalization.frameSign_boundaryOrient_of_generator,
  Polyfold.SBLocalization.boundaryBranchedMeasureDim1_cylEnd_of_pointMatched,
  Polyfold.TrivialBundle.equiv_negStructure_epStructure,
  Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq_two_structures,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_hypotheses_twoPointSection,
  Polyfold.TrivialBundle.exists_isCanonical_twoPointSection,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_twoPointSection,
  Polyfold.StrongBundleLocalizationExamples.corollary_15_4_4_index_zero_hypotheses_z3,
  Polyfold.StrongBundleLocalizationExamples.corollary_15_4_4_index_zero_z3,
  Polyfold.StrongBundleLocalizationExamples.indexZeroInput_z3OrientationRep,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_two_perturbations,
  Polyfold.PolyfoldClass.PointSuborbifold.count_eq_of_hasCobordism,
  Polyfold.PolyfoldClass.PointSuborbifold.countEff_eq_of_hasCobordismEff,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_of_model,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_of_model_statement,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_hcob_witness,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_of_model,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_hcob_witness,
  Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq,
  Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq_two_models,
  Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_iff_of_correspondence,
  Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_generalPosition_iff_of_correspondence,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence_generalPosition,
  Polyfold.StrongPolyfoldBundle.pointOrientedRep_rel_of_diagram,
  Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_of_diagram,
  Polyfold.StrongBundleLocalizationExamples.theorem_16_6_6_index_zero_correspondence_z3,
  Polyfold.StrongBundleLocalizationExamples.pullOr_ofHom_z3InvHom,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_exists,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined,
  Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation,
  Polyfold.StrongPolyfoldBundle.isTransversalPerturbation_of_isAdmissible_point,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_solutionSet_of_bump,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_count_eq,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible_wellDefined,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_norm_one,
  Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_indexZeroInput_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_inherited_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_exists_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined_all,
  Polyfold.PolyfoldClass.PointSuborbifold.count_eq_of_hasCobordism_all,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence_all,
  Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_iff_of_correspondence_all,
  Polyfold.Examples.OrbifoldSquare.theorem_16_6_6_hypotheses,
  Polyfold.Examples.OrbifoldSquare.theorem_16_6_6_sq,
  Polyfold.Examples.OrbifoldSquare.not_isTransversalAt_sectionMulti,
  Polyfold.Examples.OrbifoldSquare.exists_canonical_t5,
  Polyfold.Examples.OrbifoldSquare.count_eq_two_fifths,
  Polyfold.Examples.OrbifoldSquare.count_eq_two_fifths_all]
/-- error: rt_check_soft FAIL: RoundTrip.V16_82.A_to_B_tame uses [Polyfold.StrongBundleLocalizationExamples.pullOr_ofHom_z3InvHom] -/
#guard_msgs (whitespace := lax) in
#rt_check_soft RoundTrip.V16_82.A_to_B_tame [Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_count_eq_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_solutionSet_noBumps,
  Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation_restr,
  Polyfold.SBLocalization.PointSolution.count_restr,
  Polyfold.SBLocalization.PointSolution.countEff_restr,
  Polyfold.EP.isPointTame_sub,
  Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation_loc,
  Polyfold.SBLocalization.theorem_15_4_1_cylinder_index_zero_loc,
  Polyfold.EpFunctor.isPointTame_pullSection_of,
  Polyfold.EpFunctor.pointIntegral_pull_of,
  Polyfold.EpFunctor.pointIntegralEff_pull_of,
  Polyfold.SBLocalization.exists_signed_generator_cubeOrientation_loc,
  Polyfold.SBLocalization.exists_arePointMatchedAt_of_kernelCanonical_loc,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical,
  Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_indexZeroInput,
  Polyfold.SBLocalization.hasOrientedCobordism_of_isCanonical,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented,
  Polyfold.SBLocalization.theorem_15_4_1_cylinder_index_zero,
  Polyfold.StrongPolyfoldBundle.indexZeroInput_of_canonicalInput,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical_input,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical_input,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_inherited,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_inherited,
  Polyfold.SBLocalization.exists_signed_generator_cubeOrientation,
  Polyfold.SBLocalization.frameSign_boundaryOrient_of_generator,
  Polyfold.SBLocalization.boundaryBranchedMeasureDim1_cylEnd_of_pointMatched,
  Polyfold.TrivialBundle.equiv_negStructure_epStructure,
  Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq_two_structures,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_hypotheses_twoPointSection,
  Polyfold.TrivialBundle.exists_isCanonical_twoPointSection,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_twoPointSection,
  Polyfold.StrongBundleLocalizationExamples.corollary_15_4_4_index_zero_hypotheses_z3,
  Polyfold.StrongBundleLocalizationExamples.corollary_15_4_4_index_zero_z3,
  Polyfold.StrongBundleLocalizationExamples.indexZeroInput_z3OrientationRep,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_two_perturbations,
  Polyfold.PolyfoldClass.PointSuborbifold.count_eq_of_hasCobordism,
  Polyfold.PolyfoldClass.PointSuborbifold.countEff_eq_of_hasCobordismEff,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_of_model,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_of_model_statement,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_hcob_witness,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_of_model,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_hcob_witness,
  Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq,
  Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq_two_models,
  Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_iff_of_correspondence,
  Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_generalPosition_iff_of_correspondence,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence_generalPosition,
  Polyfold.StrongPolyfoldBundle.pointOrientedRep_rel_of_diagram,
  Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_of_diagram,
  Polyfold.StrongBundleLocalizationExamples.theorem_16_6_6_index_zero_correspondence_z3,
  Polyfold.StrongBundleLocalizationExamples.pullOr_ofHom_z3InvHom,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_exists,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined,
  Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation,
  Polyfold.StrongPolyfoldBundle.isTransversalPerturbation_of_isAdmissible_point,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_solutionSet_of_bump,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_count_eq,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible_wellDefined,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_norm_one,
  Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_indexZeroInput_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_inherited_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_exists_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined_all,
  Polyfold.PolyfoldClass.PointSuborbifold.count_eq_of_hasCobordism_all,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence_all,
  Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_iff_of_correspondence_all,
  Polyfold.Examples.OrbifoldSquare.theorem_16_6_6_hypotheses,
  Polyfold.Examples.OrbifoldSquare.theorem_16_6_6_sq,
  Polyfold.Examples.OrbifoldSquare.not_isTransversalAt_sectionMulti,
  Polyfold.Examples.OrbifoldSquare.exists_canonical_t5,
  Polyfold.Examples.OrbifoldSquare.count_eq_two_fifths,
  Polyfold.Examples.OrbifoldSquare.count_eq_two_fifths_all]

#rt_check RoundTrip.V16_82.B_gives_main [Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_count_eq_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_solutionSet_noBumps,
  Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation_restr,
  Polyfold.SBLocalization.PointSolution.count_restr,
  Polyfold.SBLocalization.PointSolution.countEff_restr,
  Polyfold.EP.isPointTame_sub,
  Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation_loc,
  Polyfold.SBLocalization.theorem_15_4_1_cylinder_index_zero_loc,
  Polyfold.EpFunctor.isPointTame_pullSection_of,
  Polyfold.EpFunctor.pointIntegral_pull_of,
  Polyfold.EpFunctor.pointIntegralEff_pull_of,
  Polyfold.SBLocalization.exists_signed_generator_cubeOrientation_loc,
  Polyfold.SBLocalization.exists_arePointMatchedAt_of_kernelCanonical_loc,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical,
  Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_indexZeroInput,
  Polyfold.SBLocalization.hasOrientedCobordism_of_isCanonical,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented,
  Polyfold.SBLocalization.theorem_15_4_1_cylinder_index_zero,
  Polyfold.StrongPolyfoldBundle.indexZeroInput_of_canonicalInput,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical_input,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical_input,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_inherited,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_inherited,
  Polyfold.SBLocalization.exists_signed_generator_cubeOrientation,
  Polyfold.SBLocalization.frameSign_boundaryOrient_of_generator,
  Polyfold.SBLocalization.boundaryBranchedMeasureDim1_cylEnd_of_pointMatched,
  Polyfold.TrivialBundle.equiv_negStructure_epStructure,
  Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq_two_structures,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_hypotheses_twoPointSection,
  Polyfold.TrivialBundle.exists_isCanonical_twoPointSection,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_twoPointSection,
  Polyfold.StrongBundleLocalizationExamples.corollary_15_4_4_index_zero_hypotheses_z3,
  Polyfold.StrongBundleLocalizationExamples.corollary_15_4_4_index_zero_z3,
  Polyfold.StrongBundleLocalizationExamples.indexZeroInput_z3OrientationRep,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_two_perturbations,
  Polyfold.PolyfoldClass.PointSuborbifold.count_eq_of_hasCobordism,
  Polyfold.PolyfoldClass.PointSuborbifold.countEff_eq_of_hasCobordismEff,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_of_model,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_of_model_statement,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_hcob_witness,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_of_model,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_hcob_witness,
  Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq,
  Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq_two_models,
  Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_iff_of_correspondence,
  Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_generalPosition_iff_of_correspondence,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence_generalPosition,
  Polyfold.StrongPolyfoldBundle.pointOrientedRep_rel_of_diagram,
  Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_of_diagram,
  Polyfold.StrongBundleLocalizationExamples.theorem_16_6_6_index_zero_correspondence_z3,
  Polyfold.StrongBundleLocalizationExamples.pullOr_ofHom_z3InvHom,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_exists,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined,
  Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation,
  Polyfold.StrongPolyfoldBundle.isTransversalPerturbation_of_isAdmissible_point,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_solutionSet_of_bump,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_count_eq,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible_wellDefined,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_norm_one,
  Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_indexZeroInput_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_inherited_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_exists_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined_all,
  Polyfold.PolyfoldClass.PointSuborbifold.count_eq_of_hasCobordism_all,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence_all,
  Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_iff_of_correspondence_all,
  Polyfold.Examples.OrbifoldSquare.theorem_16_6_6_hypotheses,
  Polyfold.Examples.OrbifoldSquare.theorem_16_6_6_sq,
  Polyfold.Examples.OrbifoldSquare.not_isTransversalAt_sectionMulti,
  Polyfold.Examples.OrbifoldSquare.exists_canonical_t5,
  Polyfold.Examples.OrbifoldSquare.count_eq_two_fifths,
  Polyfold.Examples.OrbifoldSquare.count_eq_two_fifths_all]
#rt_check RoundTrip.V16_82.B_imp_B_tame [Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_count_eq_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_solutionSet_noBumps,
  Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation_restr,
  Polyfold.SBLocalization.PointSolution.count_restr,
  Polyfold.SBLocalization.PointSolution.countEff_restr,
  Polyfold.EP.isPointTame_sub,
  Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation_loc,
  Polyfold.SBLocalization.theorem_15_4_1_cylinder_index_zero_loc,
  Polyfold.EpFunctor.isPointTame_pullSection_of,
  Polyfold.EpFunctor.pointIntegral_pull_of,
  Polyfold.EpFunctor.pointIntegralEff_pull_of,
  Polyfold.SBLocalization.exists_signed_generator_cubeOrientation_loc,
  Polyfold.SBLocalization.exists_arePointMatchedAt_of_kernelCanonical_loc,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical,
  Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_indexZeroInput,
  Polyfold.SBLocalization.hasOrientedCobordism_of_isCanonical,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented,
  Polyfold.SBLocalization.theorem_15_4_1_cylinder_index_zero,
  Polyfold.StrongPolyfoldBundle.indexZeroInput_of_canonicalInput,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical_input,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical_input,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_inherited,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_inherited,
  Polyfold.SBLocalization.exists_signed_generator_cubeOrientation,
  Polyfold.SBLocalization.frameSign_boundaryOrient_of_generator,
  Polyfold.SBLocalization.boundaryBranchedMeasureDim1_cylEnd_of_pointMatched,
  Polyfold.TrivialBundle.equiv_negStructure_epStructure,
  Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq_two_structures,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_hypotheses_twoPointSection,
  Polyfold.TrivialBundle.exists_isCanonical_twoPointSection,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_twoPointSection,
  Polyfold.StrongBundleLocalizationExamples.corollary_15_4_4_index_zero_hypotheses_z3,
  Polyfold.StrongBundleLocalizationExamples.corollary_15_4_4_index_zero_z3,
  Polyfold.StrongBundleLocalizationExamples.indexZeroInput_z3OrientationRep,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_two_perturbations,
  Polyfold.PolyfoldClass.PointSuborbifold.count_eq_of_hasCobordism,
  Polyfold.PolyfoldClass.PointSuborbifold.countEff_eq_of_hasCobordismEff,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_of_model,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_of_model_statement,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_hcob_witness,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_of_model,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_hcob_witness,
  Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq,
  Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq_two_models,
  Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_iff_of_correspondence,
  Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_generalPosition_iff_of_correspondence,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence_generalPosition,
  Polyfold.StrongPolyfoldBundle.pointOrientedRep_rel_of_diagram,
  Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_of_diagram,
  Polyfold.StrongBundleLocalizationExamples.theorem_16_6_6_index_zero_correspondence_z3,
  Polyfold.StrongBundleLocalizationExamples.pullOr_ofHom_z3InvHom,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_exists,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined,
  Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation,
  Polyfold.StrongPolyfoldBundle.isTransversalPerturbation_of_isAdmissible_point,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_solutionSet_of_bump,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_count_eq,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible_wellDefined,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_norm_one,
  Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_indexZeroInput_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_inherited_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_exists_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined_all,
  Polyfold.PolyfoldClass.PointSuborbifold.count_eq_of_hasCobordism_all,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence_all,
  Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_iff_of_correspondence_all,
  Polyfold.Examples.OrbifoldSquare.theorem_16_6_6_hypotheses,
  Polyfold.Examples.OrbifoldSquare.theorem_16_6_6_sq,
  Polyfold.Examples.OrbifoldSquare.not_isTransversalAt_sectionMulti,
  Polyfold.Examples.OrbifoldSquare.exists_canonical_t5,
  Polyfold.Examples.OrbifoldSquare.count_eq_two_fifths,
  Polyfold.Examples.OrbifoldSquare.count_eq_two_fifths_all]
#rt_overlap RoundTrip.V16_82.B_gives_main [Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_count_eq_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined_unconditional,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_solutionSet_noBumps,
  Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation_restr,
  Polyfold.SBLocalization.PointSolution.count_restr,
  Polyfold.SBLocalization.PointSolution.countEff_restr,
  Polyfold.EP.isPointTame_sub,
  Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation_loc,
  Polyfold.SBLocalization.theorem_15_4_1_cylinder_index_zero_loc,
  Polyfold.EpFunctor.isPointTame_pullSection_of,
  Polyfold.EpFunctor.pointIntegral_pull_of,
  Polyfold.EpFunctor.pointIntegralEff_pull_of,
  Polyfold.SBLocalization.exists_signed_generator_cubeOrientation_loc,
  Polyfold.SBLocalization.exists_arePointMatchedAt_of_kernelCanonical_loc,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical,
  Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_indexZeroInput,
  Polyfold.SBLocalization.hasOrientedCobordism_of_isCanonical,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented,
  Polyfold.SBLocalization.theorem_15_4_1_cylinder_index_zero,
  Polyfold.StrongPolyfoldBundle.indexZeroInput_of_canonicalInput,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical_input,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical_input,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_inherited,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_inherited,
  Polyfold.SBLocalization.exists_signed_generator_cubeOrientation,
  Polyfold.SBLocalization.frameSign_boundaryOrient_of_generator,
  Polyfold.SBLocalization.boundaryBranchedMeasureDim1_cylEnd_of_pointMatched,
  Polyfold.TrivialBundle.equiv_negStructure_epStructure,
  Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq_two_structures,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_hypotheses_twoPointSection,
  Polyfold.TrivialBundle.exists_isCanonical_twoPointSection,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_twoPointSection,
  Polyfold.StrongBundleLocalizationExamples.corollary_15_4_4_index_zero_hypotheses_z3,
  Polyfold.StrongBundleLocalizationExamples.corollary_15_4_4_index_zero_z3,
  Polyfold.StrongBundleLocalizationExamples.indexZeroInput_z3OrientationRep,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_two_perturbations,
  Polyfold.PolyfoldClass.PointSuborbifold.count_eq_of_hasCobordism,
  Polyfold.PolyfoldClass.PointSuborbifold.countEff_eq_of_hasCobordismEff,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_of_model,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_of_model_statement,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_hcob_witness,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_of_model,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_hcob_witness,
  Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq,
  Polyfold.StrongPolyfoldBundle.count_eq_of_mk_eq_two_models,
  Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_iff_of_correspondence,
  Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_generalPosition_iff_of_correspondence,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence_generalPosition,
  Polyfold.StrongPolyfoldBundle.pointOrientedRep_rel_of_diagram,
  Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_of_diagram,
  Polyfold.StrongBundleLocalizationExamples.theorem_16_6_6_index_zero_correspondence_z3,
  Polyfold.StrongBundleLocalizationExamples.pullOr_ofHom_z3InvHom,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_exists,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined,
  Polyfold.SBLocalization.pointCount_eq_of_isTransversalPerturbation,
  Polyfold.StrongPolyfoldBundle.isTransversalPerturbation_of_isAdmissible_point,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_solutionSet_of_bump,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_count_eq,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_all_admissible_wellDefined,
  Polyfold.TrivialBundle.corollary_15_4_4_index_zero_norm_one,
  Polyfold.StrongPolyfoldBundle.hasOrientedCobordism_of_indexZeroInput_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_canonical_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_polyfold_canonical_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_inherited_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_exists_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_wellDefined_all,
  Polyfold.PolyfoldClass.PointSuborbifold.count_eq_of_hasCobordism_all,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented_all,
  Polyfold.StrongPolyfoldBundle.theorem_16_6_6_index_zero_correspondence_all,
  Polyfold.StrongPolyfoldBundle.isInheritedFromPoint_iff_of_correspondence_all,
  Polyfold.Examples.OrbifoldSquare.theorem_16_6_6_hypotheses,
  Polyfold.Examples.OrbifoldSquare.theorem_16_6_6_sq,
  Polyfold.Examples.OrbifoldSquare.not_isTransversalAt_sectionMulti,
  Polyfold.Examples.OrbifoldSquare.exists_canonical_t5,
  Polyfold.Examples.OrbifoldSquare.count_eq_two_fifths,
  Polyfold.Examples.OrbifoldSquare.count_eq_two_fifths_all]

end RoundTrip.V16_82
