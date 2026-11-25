import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V15_49

set_option maxSynthPendingDepth 3

/-! Round trip for V15_49 (2021 Corollary 15.4.4, p. 703, effective version: under (LUC),
`Φ^eff_{(f,o)}([ω]) = ∮_{(Λ∘f, o)} ω` is well defined).

`A` is the conjunction of the types of the item's 42 theorems (all at universe `0`, since `B`
lives on `SEP.{0}`; the six listed definitions are vocabulary).

* `A_to_B`: not proved.  Every conjunct of `A` that yields the existence of a canonically oriented
  regular perturbation or the well-definedness of `∮` assumes, besides `B`'s hypotheses, tame germ
  data `A.B.IsScFredholmSectionTame f` and sc-smooth bump functions on `X`
  (`AdmitsBumpFunctionsPointwise`, or partitions of unity), and for the cobordism
  `(A.cubeSEP 1).B.HasScPlusSectionsThrough`; `B` grants none of these.  `B` also makes the
  index-`0` claim (weighted counts `countEff`).
* `B_to_A`: not proved.  `A` contains proof-step lemmas (local end identities, cylinder boundary
  identities, `isLUC_cubeProd`, `boundaryMeasureEff_spec`, ...) and the non-effective
  `corollary_15_4_4_wellDefined` (existence in general position) that do not follow from `B`.
* Main conjunct `corollary_15_4_4_eff_oriented_collar_all`: `B_to_main` proves `B ⇒` it.  The
  conjunct has no compactness hypothesis on `|S_f|`, which `B` needs; it is recovered from any
  regular perturbation (`(N, U)` controls compactness ⇒ `|S_f|` compact,
  `hasCompactSolutionSetEp_of_controlsCompactness`), and the statement only speaks about such
  perturbations.  The converse is not proved: the conjunct assumes `hft`, `hbump`, `hsec'` and
  (LUC) on `[0, 1] × X`, and claims neither existence nor anything in index `0`.
-/

namespace RoundTrip.V15_49
open Polyfold Polyfold.SBLocalization Polyfold.EpGroupoid

/-- The project's statement: the conjunction of the item's theorems at universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_oriented_collar.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_collar.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_collar_of_admits.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasOrientedCobordismEff_collar.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_oriented.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_loc.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_canonicalOrientation.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_cubeOrientation.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isLUC_cubeProd.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isLUC_cubeSEP.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_of_rel_onto.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.card_effIsotropy_cubeProd.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isLocalEndIdentityEff_of_matched.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isCylinderBoundaryEffOf_of_matched.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_of_matchedOrientations.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isLocalEndIdentityEff_of_structures.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_of_local_ends.{0}) ∧
  (type_of% @Polyfold.EP.boundaryMeasureEff_spec.{0}) ∧
  (type_of% @Polyfold.SBLocalization.isCylinderBoundaryEffOf_of_local.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_of_canonical.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_of_or.{0}) ∧
  (type_of% @Polyfold.SBLocalization.tameBranchedIntegralEff_zero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integralEff_eq_of_cobordism.{0}) ∧
  (type_of% @Polyfold.SBLocalization.OrientedRegularPerturbation.hasOrientedCobordismEff_refl.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integralEff_d_eq_zero_of_degIndex_eq_zero.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasOrientedCobordismEff_of_cylinder.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_cylinder_hyp.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_wellDefined.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_index_zero_wellDefined.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_oriented_collar_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_collar_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasOrientedCobordismEff_collar_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasOrientedCobordismEff_of_cylinder_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integralEff_eq_of_cobordism_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integralEff_d_eq_zero_of_degIndex_eq_zero_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_hyp_all.{0}) ∧
  (type_of% @Polyfold.EP.theorem_9_5_18_dim1_isLUC_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_loc_all.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation.{0}) ∧
  (type_of% @Polyfold.SBLocalization.Adm.boundaryMeasureEff_cylEnd_of_local.{0})

theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.corollary_15_4_4_eff_oriented_collar.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_eff_collar.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_eff_collar_of_admits.{0},
    @Polyfold.SBLocalization.hasOrientedCobordismEff_collar.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_eff_oriented.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_eff_loc.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_eff_canonicalOrientation.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_eff_cubeOrientation.{0},
    @Polyfold.EpGroupoid.isLUC_cubeProd.{0},
    @Polyfold.SBLocalization.isLUC_cubeSEP.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_eff_of_rel_onto.{0},
    @Polyfold.EpGroupoid.card_effIsotropy_cubeProd.{0},
    @Polyfold.SBLocalization.isLocalEndIdentityEff_of_matched.{0},
    @Polyfold.SBLocalization.isCylinderBoundaryEffOf_of_matched.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_eff_of_matchedOrientations.{0},
    @Polyfold.SBLocalization.isLocalEndIdentityEff_of_structures.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_eff_of_local_ends.{0},
    @Polyfold.EP.boundaryMeasureEff_spec.{0},
    @Polyfold.SBLocalization.isCylinderBoundaryEffOf_of_local.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_eff_of_canonical.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_eff_of_or.{0},
    @Polyfold.SBLocalization.tameBranchedIntegralEff_zero.{0},
    @Polyfold.SBLocalization.integralEff_eq_of_cobordism.{0},
    @Polyfold.SBLocalization.OrientedRegularPerturbation.hasOrientedCobordismEff_refl.{0},
    @Polyfold.SBLocalization.integralEff_d_eq_zero_of_degIndex_eq_zero.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_eff_hyp.{0},
    @Polyfold.SBLocalization.hasOrientedCobordismEff_of_cylinder.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_eff_cylinder_hyp.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_wellDefined.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_index_zero_wellDefined.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_eff_oriented_collar_all.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_eff_collar_all.{0},
    @Polyfold.SBLocalization.hasOrientedCobordismEff_collar_all.{0},
    @Polyfold.SBLocalization.hasOrientedCobordismEff_of_cylinder_all.{0},
    @Polyfold.SBLocalization.integralEff_eq_of_cobordism_all.{0},
    @Polyfold.SBLocalization.integralEff_d_eq_zero_of_degIndex_eq_zero_all.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_eff_hyp_all.{0},
    @Polyfold.EP.theorem_9_5_18_dim1_isLUC_all.{0},
    @Polyfold.SBLocalization.corollary_15_4_4_eff_loc_all.{0},
    @Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation.{0},
    @Polyfold.SBLocalization.Adm.boundaryMeasureEff_cylEnd_of_local.{0}⟩

/-- `∮ 0 = 0` (the project's `tameBranchedIntegralEff_zero`, re-proved: it is on the item's
list). -/
theorem tameBranchedIntegralEff_zero' {B : EP.{0}} {n : ℕ} (hn : 0 < n) {Θ : B.Obj → ℚ}
    {T : B.Obj → B.X.PObj.OrTangent →₀ ℚ} (hΘ : B.X.IsBranchedEpSubgroupoid Θ)
    (hcpt : B.X.IsCompactBranched Θ) (hT : B.X.IsOrientation Θ T)
    (hloc : ∀ x ∈ EpGroupoid.supp Θ,
      ∃ C : B.X.OrientedTameStructure n Θ x, C.Represents T ∧ C.rep.HasLUC) :
    (B.epFormsInftyEval n).tameBranchedIntegralEff hn hΘ hcpt hT hloc 0 = 0 := by
  simp only [FormEval.tameBranchedIntegralEff, FormEval.concreteBranchedIntegralEff,
    branchedIntegralEff, map_zero]
  rfl

theorem integralEff_zero' {A : SEP.{0}} {f : A.Obj → A.W} {m : ℕ} (hL : A.X.IsLUC)
    (P : OrientedRegularPerturbation A f m) : P.integralEff hL 0 = 0 :=
  tameBranchedIntegralEff_zero' _ _ _ _ _

set_option maxHeartbeats 2000000 in
/-- An exact form has class `0`. -/
theorem cls_d (A : SEP.{0}) (m : ℕ) (η : A.baseEP.epFormsInfty m) :
    cls A (m + 1) (A.baseEP.epFormsInftyD m η)
        (LinearMap.mem_ker.2 (A.baseEP.epFormsInftyD_epFormsInftyD m η)) =
      cls A (m + 1) 0 (Submodule.zero_mem _) := by
  have hmem : A.baseEP.epFormsInftyD m η ∈ A.baseEP.epFormsInftyDRange (m + 1) := ⟨η, rfl⟩
  have hz : (0 : A.baseEP.epFormsInfty (m + 1)) ∈ A.baseEP.epFormsInftyDRange (m + 1) :=
    Submodule.zero_mem _
  exact ((Submodule.Quotient.mk_eq_zero ((A.baseEP.epFormsInftyDRange (m + 1)).comap
      (LinearMap.ker (A.baseEP.epFormsInftyD (m + 1))).subtype) (x := ⟨_, _⟩)).2 hmem).trans
    ((Submodule.Quotient.mk_eq_zero ((A.baseEP.epFormsInftyDRange (m + 1)).comap
      (LinearMap.ker (A.baseEP.epFormsInftyD (m + 1))).subtype) (x := ⟨_, _⟩)).2 hz).symm

/-- A pair `(N, U)` controlling compactness forces `|S_f|` compact: `|S_f|` is closed (`S_f` is
closed and saturated) and lies in the compact `cl |{x ∈ U | N(f(x)) ≤ 1}|`. -/
theorem hasCompactSolutionSetEp_of_controlsCompactness {A : SEP.{0}} {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) {N : A.B.One → ℝ} {U : Set A.Obj}
    (hcc : ControlsCompactness A f N U) : A.E.HasCompactSolutionSetEp f := by
  obtain ⟨⟨hsm, hfun⟩, -⟩ := hf
  obtain ⟨hN, -, -, hSU, hK⟩ := hcc
  have hsat : A.X.IsSaturated (solutionSet A.P f) := A.X.isSaturated_iff.2 fun φ hφ => by
    show f (A.X.tgt φ) = fiberZero A.P (A.X.tgt φ)
    rw [hfun φ]
    have e : EpStrongBundle.sectionPair hsm.1 φ =
        ⟨(φ, fiberZero A.P (A.X.src φ)), isSection_fiberZero (A.X.src φ)⟩ :=
      Subtype.ext (Prod.ext rfl hφ)
    rw [e, A.E.μ_fiberZero]
  have hcl := A.X.isClosed_image_π_of_isSaturated hsat (isClosed_solutionSet hsm)
  refine hK.of_isClosed_subset hcl ?_
  rintro _ ⟨x, hx, rfl⟩
  exact subset_closure
    ⟨x, ⟨hSU hx, (hN.isAuxNorm.auxLe_fiberZero x zero_le_one).congr hx.symm⟩, rfl⟩

/-- **`B` ⇒ the main conjunct `corollary_15_4_4_eff_oriented_collar_all`.** -/
theorem B_to_main (hB : B) :
    type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_oriented_collar_all.{0} := by
  intro A f hd hf _hft hsec _hsec' o ho hinv m hidx hpara _hbump hLUC _hLUCC
  have := paracompactSpace_rn_prod A.X.PObj
  have := paracompactSpace_rn_pullback A.B
  have key : ∀ P : OrientedRegularPerturbation A f m, ∃ Φ : A.baseEP.epDeRham (m + 1) → ℝ,
      ∀ P' : OrientedRegularPerturbation A f m, IsCanonicalFor P'.Λ hf.2 hsec o (m + 1) P'.T →
      ∀ (ω : A.baseEP.epFormsInfty (m + 1)) (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD _)),
        Φ (cls A (m + 1) ω hω) = P'.integralEff hLUC ω := fun P =>
    ((hB A hd hpara hLUC f hf (hasCompactSolutionSetEp_of_controlsCompactness hf P.isRegular.1)
      hsec o ho hinv).1 m hidx).2
  refine ⟨fun P hP η => ?_, fun P₀ P₁ h₀ h₁ ω hω => ?_⟩
  · obtain ⟨Φ, hΦ⟩ := key P
    have h1 := hΦ P hP (A.baseEP.epFormsInftyD m η)
      (LinearMap.mem_ker.2 (A.baseEP.epFormsInftyD_epFormsInftyD m η))
    have h0 := hΦ P hP 0 (Submodule.zero_mem _)
    rw [← h1, cls_d, h0, integralEff_zero']
  · obtain ⟨Φ, hΦ⟩ := key P₀
    exact (hΦ P₀ h₀ ω (LinearMap.mem_ker.2 hω)).symm.trans
      (hΦ P₁ h₁ ω (LinearMap.mem_ker.2 hω))

#rt_check RoundTrip.V15_49.B_to_main [Polyfold.SBLocalization.corollary_15_4_4_eff_oriented_collar,
  Polyfold.SBLocalization.corollary_15_4_4_eff_collar,
  Polyfold.SBLocalization.corollary_15_4_4_eff_collar_of_admits,
  Polyfold.SBLocalization.hasOrientedCobordismEff_collar,
  Polyfold.SBLocalization.corollary_15_4_4_eff_oriented,
  Polyfold.SBLocalization.corollary_15_4_4_eff_loc,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented,
  Polyfold.SBLocalization.corollary_15_4_4_eff_canonicalOrientation,
  Polyfold.SBLocalization.corollary_15_4_4_eff_cubeOrientation,
  Polyfold.EpGroupoid.isLUC_cubeProd,
  Polyfold.SBLocalization.isLUC_cubeSEP,
  Polyfold.SBLocalization.corollary_15_4_4_eff_of_rel_onto,
  Polyfold.EpGroupoid.card_effIsotropy_cubeProd,
  Polyfold.SBLocalization.isLocalEndIdentityEff_of_matched,
  Polyfold.SBLocalization.isCylinderBoundaryEffOf_of_matched,
  Polyfold.SBLocalization.corollary_15_4_4_eff_of_matchedOrientations,
  Polyfold.SBLocalization.isLocalEndIdentityEff_of_structures,
  Polyfold.SBLocalization.corollary_15_4_4_eff_of_local_ends,
  Polyfold.EP.boundaryMeasureEff_spec,
  Polyfold.SBLocalization.isCylinderBoundaryEffOf_of_local,
  Polyfold.SBLocalization.corollary_15_4_4_eff_of_canonical,
  Polyfold.SBLocalization.corollary_15_4_4_eff_of_or,
  Polyfold.SBLocalization.tameBranchedIntegralEff_zero,
  Polyfold.SBLocalization.integralEff_eq_of_cobordism,
  Polyfold.SBLocalization.OrientedRegularPerturbation.hasOrientedCobordismEff_refl,
  Polyfold.SBLocalization.integralEff_d_eq_zero_of_degIndex_eq_zero,
  Polyfold.SBLocalization.corollary_15_4_4_eff_hyp,
  Polyfold.SBLocalization.hasOrientedCobordismEff_of_cylinder,
  Polyfold.SBLocalization.corollary_15_4_4_eff_cylinder_hyp,
  Polyfold.SBLocalization.corollary_15_4_4_wellDefined,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_wellDefined,
  Polyfold.SBLocalization.corollary_15_4_4_eff_oriented_collar_all,
  Polyfold.SBLocalization.corollary_15_4_4_eff_collar_all,
  Polyfold.SBLocalization.hasOrientedCobordismEff_collar_all,
  Polyfold.SBLocalization.hasOrientedCobordismEff_of_cylinder_all,
  Polyfold.SBLocalization.integralEff_eq_of_cobordism_all,
  Polyfold.SBLocalization.integralEff_d_eq_zero_of_degIndex_eq_zero_all,
  Polyfold.SBLocalization.corollary_15_4_4_eff_hyp_all,
  Polyfold.EP.theorem_9_5_18_dim1_isLUC_all,
  Polyfold.SBLocalization.corollary_15_4_4_eff_loc_all,
  Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation,
  Polyfold.SBLocalization.Adm.boundaryMeasureEff_cylEnd_of_local]
#rt_overlap RoundTrip.V15_49.B_to_main [Polyfold.SBLocalization.corollary_15_4_4_eff_oriented_collar,
  Polyfold.SBLocalization.corollary_15_4_4_eff_collar,
  Polyfold.SBLocalization.corollary_15_4_4_eff_collar_of_admits,
  Polyfold.SBLocalization.hasOrientedCobordismEff_collar,
  Polyfold.SBLocalization.corollary_15_4_4_eff_oriented,
  Polyfold.SBLocalization.corollary_15_4_4_eff_loc,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented,
  Polyfold.SBLocalization.corollary_15_4_4_eff_canonicalOrientation,
  Polyfold.SBLocalization.corollary_15_4_4_eff_cubeOrientation,
  Polyfold.EpGroupoid.isLUC_cubeProd,
  Polyfold.SBLocalization.isLUC_cubeSEP,
  Polyfold.SBLocalization.corollary_15_4_4_eff_of_rel_onto,
  Polyfold.EpGroupoid.card_effIsotropy_cubeProd,
  Polyfold.SBLocalization.isLocalEndIdentityEff_of_matched,
  Polyfold.SBLocalization.isCylinderBoundaryEffOf_of_matched,
  Polyfold.SBLocalization.corollary_15_4_4_eff_of_matchedOrientations,
  Polyfold.SBLocalization.isLocalEndIdentityEff_of_structures,
  Polyfold.SBLocalization.corollary_15_4_4_eff_of_local_ends,
  Polyfold.EP.boundaryMeasureEff_spec,
  Polyfold.SBLocalization.isCylinderBoundaryEffOf_of_local,
  Polyfold.SBLocalization.corollary_15_4_4_eff_of_canonical,
  Polyfold.SBLocalization.corollary_15_4_4_eff_of_or,
  Polyfold.SBLocalization.tameBranchedIntegralEff_zero,
  Polyfold.SBLocalization.integralEff_eq_of_cobordism,
  Polyfold.SBLocalization.OrientedRegularPerturbation.hasOrientedCobordismEff_refl,
  Polyfold.SBLocalization.integralEff_d_eq_zero_of_degIndex_eq_zero,
  Polyfold.SBLocalization.corollary_15_4_4_eff_hyp,
  Polyfold.SBLocalization.hasOrientedCobordismEff_of_cylinder,
  Polyfold.SBLocalization.corollary_15_4_4_eff_cylinder_hyp,
  Polyfold.SBLocalization.corollary_15_4_4_wellDefined,
  Polyfold.SBLocalization.corollary_15_4_4_index_zero_wellDefined,
  Polyfold.SBLocalization.corollary_15_4_4_eff_oriented_collar_all,
  Polyfold.SBLocalization.corollary_15_4_4_eff_collar_all,
  Polyfold.SBLocalization.hasOrientedCobordismEff_collar_all,
  Polyfold.SBLocalization.hasOrientedCobordismEff_of_cylinder_all,
  Polyfold.SBLocalization.integralEff_eq_of_cobordism_all,
  Polyfold.SBLocalization.integralEff_d_eq_zero_of_degIndex_eq_zero_all,
  Polyfold.SBLocalization.corollary_15_4_4_eff_hyp_all,
  Polyfold.EP.theorem_9_5_18_dim1_isLUC_all,
  Polyfold.SBLocalization.corollary_15_4_4_eff_loc_all,
  Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation,
  Polyfold.SBLocalization.Adm.boundaryMeasureEff_cylEnd_of_local]

end RoundTrip.V15_49
