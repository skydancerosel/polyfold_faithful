import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V15_49
import Polyfold.Chapter16.Corollary1544NoSectionsDeRham

set_option maxSynthPendingDepth 3

/-! Round trip for V15_49_r2 (refresh of V15_49: 2021 Corollary 15.4.4, p. 703, effective version:
under (LUC), `Φ^eff_{(f,o)}([ω]) = ∮_{(Λ∘f, o)} ω` is well defined).  `B` is the existing blind
statement `RoundTrip.V15_49.B`.

* `A`: the types of the 17 theorems of `Chapter16/Corollary1544NoSections*` and of the row's 42
  theorems (universe `0`).  The new theorems drop `(A.cubeSEP 1).B.HasScPlusSectionsThrough` and
  (LUC) on `[0, 1] × X`, which follow from bump functions and (LUC) on `X`, and state the
  corollary as maps on `H^k_dR(X) = EP.epDeRham`.
* Main conjuncts `Amain`: `corollary_15_4_4_eff_deRham ∧ corollary_15_4_4_index_zero_eff_deRham`.
* `B_to_main`: proved.  `Bplus` (`B` with tame germ data `hft` and bump functions `hbump` added):
  `main_to_Bplus` and `Bplus_to_main` proved, hence `A_to_Bplus`.  The statements differ exactly
  by `hft` and `hbump` (§15.3, 2021 p. 692); Corollary 15.4.4 names neither.
* `A_to_B`, `B_to_A`: not proved (as for V15_37_r2).
* `#rt_check` of `A_to_Bplus` bans `A`'s theorems except `isLUC_cubeSEP` and `isLUC_cubeProd`,
  which the types of two conjuncts of `A` mention; its proof is `main_to_Bplus` (checked against
  the full list) applied to two conjuncts of `A`.
-/

namespace RoundTrip.V15_49_r2
open Polyfold Polyfold.SBLocalization

abbrev B : Prop := RoundTrip.V15_49.B

/-- The project's statement: the new theorems (`Chapter16/Corollary1544NoSections*`) and the
row's theorems, at universe `0`. -/
def A : Prop :=
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_deRham.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_index_zero_deRham.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_deRham.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_index_zero_eff_deRham.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_oriented_bump.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_oriented_bump.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_wellDefined_bump.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_loc_bump.{0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_loc_bump.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation_bump.{0}) ∧
  (type_of% @Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation_bump.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasScPlusSectionsThrough_cubeSEP_of_bump.{0}) ∧
  (type_of% @Polyfold.SBLocalization.hasScPlusSectionsThrough_of_bump.{0}) ∧
  (type_of% @Polyfold.SBLocalization.OrientedRegularPerturbation.integral_sub.{0}) ∧
  (type_of% @Polyfold.SBLocalization.OrientedRegularPerturbation.integralEff_sub.{0}) ∧
  (type_of% @Polyfold.SBLocalization.exists_deRham_map.{0,0}) ∧
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_deRham_planeZ3) ∧
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

set_option maxHeartbeats 4000000 in
theorem A_holds : A :=
  ⟨@Polyfold.SBLocalization.corollary_15_4_4_deRham.{0},
   @Polyfold.SBLocalization.corollary_15_4_4_index_zero_deRham.{0},
   @Polyfold.SBLocalization.corollary_15_4_4_eff_deRham.{0},
   @Polyfold.SBLocalization.corollary_15_4_4_index_zero_eff_deRham.{0},
   @Polyfold.SBLocalization.corollary_15_4_4_oriented_bump.{0},
   @Polyfold.SBLocalization.corollary_15_4_4_eff_oriented_bump.{0},
   @Polyfold.SBLocalization.corollary_15_4_4_wellDefined_bump.{0},
   @Polyfold.SBLocalization.corollary_15_4_4_loc_bump.{0},
   @Polyfold.SBLocalization.corollary_15_4_4_eff_loc_bump.{0},
   @Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation_bump.{0},
   @Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation_bump.{0},
   @Polyfold.SBLocalization.hasScPlusSectionsThrough_cubeSEP_of_bump.{0},
   @Polyfold.SBLocalization.hasScPlusSectionsThrough_of_bump.{0},
   @Polyfold.SBLocalization.OrientedRegularPerturbation.integral_sub.{0},
   @Polyfold.SBLocalization.OrientedRegularPerturbation.integralEff_sub.{0},
   @Polyfold.SBLocalization.exists_deRham_map.{0,0},
   @Polyfold.SBLocalization.corollary_15_4_4_deRham_planeZ3,
   @Polyfold.SBLocalization.corollary_15_4_4_eff_oriented_collar.{0},
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

/-- The main conjuncts. -/
def Amain : Prop :=
  (type_of% @Polyfold.SBLocalization.corollary_15_4_4_eff_deRham.{0}) ∧ (type_of% @Polyfold.SBLocalization.corollary_15_4_4_index_zero_eff_deRham.{0})

/-- `B` with the two hypotheses of the project's forms that `B` does not state: tame germ data
`A.B.IsScFredholmSectionTame f` and sc-smooth bump functions `A.X.AdmitsBumpFunctionsPointwise`
(the standing assumption of §15.3, 2021 p. 692). -/
def Bplus : Prop :=
  ∀ (A : SEP.{0}) [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × A.Obj)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace A.P (Prod.snd : (Fin n → ℝ) × A.Obj → A.Obj))],
    (∀ x : A.Obj, A.X.PObj.degIndex x = 0) → A.X.HasParacompactOrbitSpace →
    A.X.AdmitsBumpFunctionsPointwise →
    ∀ hL : A.X.IsLUC,
    ∀ (f : A.Obj → A.W) (hF : A.E.IsScFredholmSectionFunctor f),
      A.B.IsScFredholmSectionTame f →
      A.E.HasCompactSolutionSetEp f →
    ∀ (hsec : A.B.HasScPlusSectionsThrough)
      (o : (y : A.Obj) → (hy : y ∈ A.X.PObj.smoothSet) → Orx f hF.2 y hy),
      IsSectionOrientation f hF.2 o → A.E.IsOrInvariant hF hsec o →
      -- index `m + 1 ≥ 1`
      (∀ m : ℕ, (∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ)) →
        (∃ P : OrientedRegularPerturbation A f m, IsCanonicalFor P.Λ hF.2 hsec o (m + 1) P.T) ∧
        ∃ Φ : A.baseEP.epDeRham (m + 1) → ℝ,
          ∀ P : OrientedRegularPerturbation A f m, IsCanonicalFor P.Λ hF.2 hsec o (m + 1) P.T →
          ∀ (ω : A.baseEP.epFormsInfty (m + 1)) (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD _)),
            Φ (RoundTrip.V15_49.cls A (m + 1) ω hω) = P.integralEff hL ω) ∧
      -- index `0`
      ((∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x 0) →
        (∃ P : PointPerturbation A f, P.IsCanonical hF.2 hsec o) ∧
        ∃ Φ : A.baseEP.epDeRham 0 → ℝ,
          ∀ P : PointPerturbation A f, P.IsCanonical hF.2 hsec o →
          ∀ (ω : A.baseEP.epFormsInfty 0) (hω : ω ∈ LinearMap.ker (A.baseEP.epFormsInftyD 0)),
            Φ (RoundTrip.V15_49.cls A 0 ω hω) = P.countEff hL ω)

set_option maxHeartbeats 4000000 in
/-- **`B` ⇒ the main conjuncts.** -/
theorem B_to_main (hB : B) : Amain := by
  refine ⟨?_, ?_⟩
  · intro A f hd hf _hft hsec o ho hinv m hidx hpara _hbump hS hL
    have := paracompactSpace_rn_prod A.X.PObj
    have := paracompactSpace_rn_pullback A.B
    exact (hB A hd hpara hL f hf hS hsec o ho hinv).1 m hidx
  · intro A f hd hf _hft hsec o ho hinv hidx hpara _hbump hS hL
    have := paracompactSpace_rn_prod A.X.PObj
    have := paracompactSpace_rn_pullback A.B
    exact (hB A hd hpara hL f hf hS hsec o ho hinv).2 hidx

set_option maxHeartbeats 4000000 in
/-- **The main conjuncts ⇒ `B` with `hft` and `hbump`.** -/
theorem main_to_Bplus (h : Amain) : Bplus := by
  intro A _ _ hd hpara hbump hL f hF hft hS hsec o ho hinv
  exact ⟨fun m hidx => h.1 hd hF hft hsec o ho hinv hidx hpara hbump hS hL,
    fun hidx => h.2 hd hF hft hsec o ho hinv hidx hpara hbump hS hL⟩

set_option maxHeartbeats 4000000 in
/-- **`B` with `hft` and `hbump` ⇒ the main conjuncts** (so `Amain ↔ Bplus`). -/
theorem Bplus_to_main (hB : Bplus) : Amain := by
  refine ⟨?_, ?_⟩
  · intro A f hd hf hft hsec o ho hinv m hidx hpara hbump hS hL
    have := paracompactSpace_rn_prod A.X.PObj
    have := paracompactSpace_rn_pullback A.B
    exact (hB A hd hpara hbump hL f hf hft hS hsec o ho hinv).1 m hidx
  · intro A f hd hf hft hsec o ho hinv hidx hpara hbump hS hL
    have := paracompactSpace_rn_prod A.X.PObj
    have := paracompactSpace_rn_pullback A.B
    exact (hB A hd hpara hbump hL f hf hft hS hsec o ho hinv).2 hidx

theorem B_to_Bplus (hB : B) : Bplus := main_to_Bplus (B_to_main hB)

/-- **`A` ⇒ `B` with `hft` and `hbump`.** -/
theorem A_to_Bplus (hA : A) : Bplus := main_to_Bplus ⟨hA.2.2.1, hA.2.2.2.1⟩

set_option hygiene false in
/-- `#rt_check` of `t` against all of `A`'s theorems. -/
macro "rt_check_A " t:ident : command => `(#rt_check $t [
    Polyfold.SBLocalization.corollary_15_4_4_deRham,
    Polyfold.SBLocalization.corollary_15_4_4_index_zero_deRham,
    Polyfold.SBLocalization.corollary_15_4_4_eff_deRham,
    Polyfold.SBLocalization.corollary_15_4_4_index_zero_eff_deRham,
    Polyfold.SBLocalization.corollary_15_4_4_oriented_bump,
    Polyfold.SBLocalization.corollary_15_4_4_eff_oriented_bump,
    Polyfold.SBLocalization.corollary_15_4_4_wellDefined_bump,
    Polyfold.SBLocalization.corollary_15_4_4_loc_bump,
    Polyfold.SBLocalization.corollary_15_4_4_eff_loc_bump,
    Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation_bump,
    Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation_bump,
    Polyfold.SBLocalization.hasScPlusSectionsThrough_cubeSEP_of_bump,
    Polyfold.SBLocalization.hasScPlusSectionsThrough_of_bump,
    Polyfold.SBLocalization.OrientedRegularPerturbation.integral_sub,
    Polyfold.SBLocalization.OrientedRegularPerturbation.integralEff_sub,
    Polyfold.SBLocalization.exists_deRham_map,
    Polyfold.SBLocalization.corollary_15_4_4_deRham_planeZ3,
    Polyfold.SBLocalization.corollary_15_4_4_eff_oriented_collar,
    Polyfold.SBLocalization.corollary_15_4_4_eff_collar,
    Polyfold.SBLocalization.corollary_15_4_4_eff_collar_of_admits,
    Polyfold.SBLocalization.hasOrientedCobordismEff_collar,
    Polyfold.SBLocalization.corollary_15_4_4_eff_oriented,
    Polyfold.SBLocalization.corollary_15_4_4_eff_loc,
    Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented,
    Polyfold.SBLocalization.corollary_15_4_4_eff_canonicalOrientation,
    Polyfold.SBLocalization.corollary_15_4_4_eff_cubeOrientation,
    Polyfold.EpGroupoid.isLUC_cubeProd, Polyfold.SBLocalization.isLUC_cubeSEP,
    Polyfold.SBLocalization.corollary_15_4_4_eff_of_rel_onto,
    Polyfold.EpGroupoid.card_effIsotropy_cubeProd,
    Polyfold.SBLocalization.isLocalEndIdentityEff_of_matched,
    Polyfold.SBLocalization.isCylinderBoundaryEffOf_of_matched,
    Polyfold.SBLocalization.corollary_15_4_4_eff_of_matchedOrientations,
    Polyfold.SBLocalization.isLocalEndIdentityEff_of_structures,
    Polyfold.SBLocalization.corollary_15_4_4_eff_of_local_ends,
    Polyfold.EP.boundaryMeasureEff_spec, Polyfold.SBLocalization.isCylinderBoundaryEffOf_of_local,
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
    Polyfold.SBLocalization.Adm.boundaryMeasureEff_cylEnd_of_local])

set_option hygiene false in
/-- `#rt_check` of `t` against `A`'s theorems except `isLUC_cubeSEP`, `isLUC_cubeProd`,
which occur in the statement of `A` itself (in the types of
`corollary_15_4_4_eff_of_rel_onto` and `corollary_15_4_4_eff_of_or`), so that every proof
mentioning `A` reaches them. -/
macro "rt_check_A_stmt " t:ident : command => `(#rt_check $t [
    Polyfold.SBLocalization.corollary_15_4_4_deRham,
    Polyfold.SBLocalization.corollary_15_4_4_index_zero_deRham,
    Polyfold.SBLocalization.corollary_15_4_4_eff_deRham,
    Polyfold.SBLocalization.corollary_15_4_4_index_zero_eff_deRham,
    Polyfold.SBLocalization.corollary_15_4_4_oriented_bump,
    Polyfold.SBLocalization.corollary_15_4_4_eff_oriented_bump,
    Polyfold.SBLocalization.corollary_15_4_4_wellDefined_bump,
    Polyfold.SBLocalization.corollary_15_4_4_loc_bump,
    Polyfold.SBLocalization.corollary_15_4_4_eff_loc_bump,
    Polyfold.SBLocalization.integral_eq_of_isTransversalPerturbation_bump,
    Polyfold.SBLocalization.integralEff_eq_of_isTransversalPerturbation_bump,
    Polyfold.SBLocalization.hasScPlusSectionsThrough_cubeSEP_of_bump,
    Polyfold.SBLocalization.hasScPlusSectionsThrough_of_bump,
    Polyfold.SBLocalization.OrientedRegularPerturbation.integral_sub,
    Polyfold.SBLocalization.OrientedRegularPerturbation.integralEff_sub,
    Polyfold.SBLocalization.exists_deRham_map,
    Polyfold.SBLocalization.corollary_15_4_4_deRham_planeZ3,
    Polyfold.SBLocalization.corollary_15_4_4_eff_oriented_collar,
    Polyfold.SBLocalization.corollary_15_4_4_eff_collar,
    Polyfold.SBLocalization.corollary_15_4_4_eff_collar_of_admits,
    Polyfold.SBLocalization.hasOrientedCobordismEff_collar,
    Polyfold.SBLocalization.corollary_15_4_4_eff_oriented,
    Polyfold.SBLocalization.corollary_15_4_4_eff_loc,
    Polyfold.SBLocalization.corollary_15_4_4_index_zero_oriented,
    Polyfold.SBLocalization.corollary_15_4_4_eff_canonicalOrientation,
    Polyfold.SBLocalization.corollary_15_4_4_eff_cubeOrientation,
    Polyfold.SBLocalization.corollary_15_4_4_eff_of_rel_onto,
    Polyfold.EpGroupoid.card_effIsotropy_cubeProd,
    Polyfold.SBLocalization.isLocalEndIdentityEff_of_matched,
    Polyfold.SBLocalization.isCylinderBoundaryEffOf_of_matched,
    Polyfold.SBLocalization.corollary_15_4_4_eff_of_matchedOrientations,
    Polyfold.SBLocalization.isLocalEndIdentityEff_of_structures,
    Polyfold.SBLocalization.corollary_15_4_4_eff_of_local_ends,
    Polyfold.EP.boundaryMeasureEff_spec, Polyfold.SBLocalization.isCylinderBoundaryEffOf_of_local,
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
    Polyfold.SBLocalization.Adm.boundaryMeasureEff_cylEnd_of_local])

rt_check_A RoundTrip.V15_49_r2.B_to_main
rt_check_A RoundTrip.V15_49_r2.main_to_Bplus
rt_check_A RoundTrip.V15_49_r2.Bplus_to_main
rt_check_A_stmt RoundTrip.V15_49_r2.A_to_Bplus

end RoundTrip.V15_49_r2
