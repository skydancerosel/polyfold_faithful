import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V12_26

set_option maxSynthPendingDepth 3

namespace RoundTrip.V12_26
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpStrongBundle.proposition_12_5_6_loc.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.proposition_12_5_6_mp_loc.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.proposition_12_5_6_mpr_loc.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.isTwoToOne_iff_loc.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.orbitProjLoc_orbitLocHomeomorph.{0}) ∧
  (type_of% @Polyfold.HalfSpaceBundle.proposition_12_5_6_loc_halfSpace) ∧
  (type_of% @Polyfold.EpStrongBundle.proposition_12_5_6_mp.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.proposition_12_5_6_mpr_invariant.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.proposition_12_5_6_mpr_hyp.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.proposition_12_5_6_mpr_hyp'.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.exists_nhds_orMor_eq_hyp.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.isOpen_orSat_hyp.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.orMor_isotropy_of_isTwoToOne.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.eq_of_quot_eq_of_isTwoToOne.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.proposition_12_5_6_of_loc.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.orbitSection_iff_loc.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.proposition_12_5_6_loc.{0},
    @Polyfold.EpStrongBundle.proposition_12_5_6_mp_loc.{0},
    @Polyfold.EpStrongBundle.proposition_12_5_6_mpr_loc.{0},
    @Polyfold.EpStrongBundle.isTwoToOne_iff_loc.{0},
    @Polyfold.EpStrongBundle.orbitProjLoc_orbitLocHomeomorph.{0},
    @Polyfold.HalfSpaceBundle.proposition_12_5_6_loc_halfSpace,
    @Polyfold.EpStrongBundle.proposition_12_5_6_mp.{0},
    @Polyfold.EpStrongBundle.proposition_12_5_6_mpr_invariant.{0},
    @Polyfold.EpStrongBundle.proposition_12_5_6_mpr_hyp.{0},
    @Polyfold.EpStrongBundle.proposition_12_5_6_mpr_hyp'.{0},
    @Polyfold.EpStrongBundle.exists_nhds_orMor_eq_hyp.{0},
    @Polyfold.EpStrongBundle.isOpen_orSat_hyp.{0},
    @Polyfold.EpStrongBundle.orMor_isotropy_of_isTwoToOne.{0},
    @Polyfold.EpStrongBundle.eq_of_quot_eq_of_isTwoToOne.{0},
    @Polyfold.EpStrongBundle.proposition_12_5_6_of_loc.{0},
    @Polyfold.EpStrongBundle.orbitSection_iff_loc.{0}⟩

/-- `B`'s "two-to-one" is the project's `IsTwoToOne`. -/
theorem isTwoToOneB_iff {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
    {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
    [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B) {f : Obj → W}
    (hF : E.IsScFredholmSectionFunctor f) (hsec : B.HasScPlusSectionsThrough) :
    IsTwoToOneB E hF hsec ↔ E.IsTwoToOne hF hsec := by
  constructor
  · intro h c
    obtain ⟨d₁, d₂, hne, hpre⟩ := h c
    have h1 : d₁ ∈ E.orbitProj hF hsec ⁻¹' {c} := hpre ▸ Or.inl rfl
    have h2 : d₂ ∈ E.orbitProj hF hsec ⁻¹' {c} := hpre ▸ Or.inr rfl
    refine ⟨d₁, d₂, hne, h1, h2, fun d hd => ?_⟩
    have : d ∈ E.orbitProj hF hsec ⁻¹' {c} := hd
    rw [hpre] at this
    exact this
  · intro h c
    obtain ⟨d₁, d₂, hne, h1, h2, hall⟩ := h c
    refine ⟨d₁, d₂, hne, Set.ext fun d => ⟨fun hd => hall d hd, ?_⟩⟩
    rintro (rfl | rfl)
    · exact h1
    · exact h2

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ E _ _ _ _ hX hbump f hF hfT hsec
  have h := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 E hF hfT hsec hX hbump
  rw [isTwoToOneB_iff]
  exact h

/-- The main conjunct `proposition_12_5_6_of_loc` follows from `B` (the other conjuncts do not). -/
theorem B_to_A_main : B → type_of% @Polyfold.EpStrongBundle.proposition_12_5_6_of_loc.{0} := by
  intro hB Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ E f hF hfT hsec _ _ _ _ hX hbump
  have h := hB Obj Mor X W P B E hX hbump f hF hfT hsec
  rw [isTwoToOneB_iff] at h
  exact h

#rt_check RoundTrip.V12_26.A_to_B [Polyfold.EpStrongBundle.proposition_12_5_6_loc,
  Polyfold.EpStrongBundle.proposition_12_5_6_mp_loc,
  Polyfold.EpStrongBundle.proposition_12_5_6_mpr_loc,
  Polyfold.EpStrongBundle.isTwoToOne_iff_loc,
  Polyfold.EpStrongBundle.orbitProjLoc_orbitLocHomeomorph,
  Polyfold.HalfSpaceBundle.proposition_12_5_6_loc_halfSpace,
  Polyfold.EpStrongBundle.proposition_12_5_6_mp,
  Polyfold.EpStrongBundle.proposition_12_5_6_mpr_invariant,
  Polyfold.EpStrongBundle.proposition_12_5_6_mpr_hyp,
  Polyfold.EpStrongBundle.proposition_12_5_6_mpr_hyp',
  Polyfold.EpStrongBundle.exists_nhds_orMor_eq_hyp,
  Polyfold.EpStrongBundle.isOpen_orSat_hyp,
  Polyfold.EpStrongBundle.orMor_isotropy_of_isTwoToOne,
  Polyfold.EpStrongBundle.eq_of_quot_eq_of_isTwoToOne,
  Polyfold.EpStrongBundle.proposition_12_5_6_of_loc,
  Polyfold.EpStrongBundle.orbitSection_iff_loc]
#rt_check RoundTrip.V12_26.B_to_A_main [Polyfold.EpStrongBundle.proposition_12_5_6_loc,
  Polyfold.EpStrongBundle.proposition_12_5_6_mp_loc,
  Polyfold.EpStrongBundle.proposition_12_5_6_mpr_loc,
  Polyfold.EpStrongBundle.isTwoToOne_iff_loc,
  Polyfold.EpStrongBundle.orbitProjLoc_orbitLocHomeomorph,
  Polyfold.HalfSpaceBundle.proposition_12_5_6_loc_halfSpace,
  Polyfold.EpStrongBundle.proposition_12_5_6_mp,
  Polyfold.EpStrongBundle.proposition_12_5_6_mpr_invariant,
  Polyfold.EpStrongBundle.proposition_12_5_6_mpr_hyp,
  Polyfold.EpStrongBundle.proposition_12_5_6_mpr_hyp',
  Polyfold.EpStrongBundle.exists_nhds_orMor_eq_hyp,
  Polyfold.EpStrongBundle.isOpen_orSat_hyp,
  Polyfold.EpStrongBundle.orMor_isotropy_of_isTwoToOne,
  Polyfold.EpStrongBundle.eq_of_quot_eq_of_isTwoToOne,
  Polyfold.EpStrongBundle.proposition_12_5_6_of_loc,
  Polyfold.EpStrongBundle.orbitSection_iff_loc]
#rt_overlap RoundTrip.V12_26.B_to_A_main [Polyfold.EpStrongBundle.proposition_12_5_6_loc,
  Polyfold.EpStrongBundle.proposition_12_5_6_mp_loc,
  Polyfold.EpStrongBundle.proposition_12_5_6_mpr_loc,
  Polyfold.EpStrongBundle.isTwoToOne_iff_loc,
  Polyfold.EpStrongBundle.orbitProjLoc_orbitLocHomeomorph,
  Polyfold.HalfSpaceBundle.proposition_12_5_6_loc_halfSpace,
  Polyfold.EpStrongBundle.proposition_12_5_6_mp,
  Polyfold.EpStrongBundle.proposition_12_5_6_mpr_invariant,
  Polyfold.EpStrongBundle.proposition_12_5_6_mpr_hyp,
  Polyfold.EpStrongBundle.proposition_12_5_6_mpr_hyp',
  Polyfold.EpStrongBundle.exists_nhds_orMor_eq_hyp,
  Polyfold.EpStrongBundle.isOpen_orSat_hyp,
  Polyfold.EpStrongBundle.orMor_isotropy_of_isTwoToOne,
  Polyfold.EpStrongBundle.eq_of_quot_eq_of_isTwoToOne,
  Polyfold.EpStrongBundle.proposition_12_5_6_of_loc,
  Polyfold.EpStrongBundle.orbitSection_iff_loc]

end RoundTrip.V12_26
