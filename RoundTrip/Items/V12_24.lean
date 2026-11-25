import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V12_24

set_option maxSynthPendingDepth 3

namespace RoundTrip.V12_24
open Polyfold

/-! Universes: A's theorems are instantiated at universe 0 (B lives in `Type`); the
`UntamedCorner` and `HalfSpaceBundle` examples have no universe parameters.

Only a partial `A → B` is proved here (`A_to_B123`: clauses (1)–(3) of `B`); clause (4), the
push-forward along an arbitrary sheet, and `B → A` are not proved (see the JSON). -/

def A : Prop :=
  (type_of% @Polyfold.EpStrongBundle.theorem_12_5_3_loc.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.theorem_12_5_3_push_loc.{0}) ∧
  (type_of% @Polyfold.orProj_two_loc.{0, 0}) ∧
  (type_of% @Polyfold.theorem_6_6_17_loc.{0, 0}) ∧
  (type_of% @Polyfold.StrongBundle.Dom.transportLoc_eq.{0, 0}) ∧
  (type_of% @Polyfold.orLocalTransportLoc_transport_eq.{0, 0}) ∧
  (type_of% @Polyfold.StrongBundle.LocalIso.orLoc_comm.{0, 0, 0, 0}) ∧
  (type_of% @Polyfold.StrongBundle.LocalIso.isContOn_pullLoc.{0, 0, 0, 0}) ∧
  (type_of% @Polyfold.UntamedCorner.theorem_12_5_3_untamed_not) ∧
  (type_of% @Polyfold.UntamedCorner.not_theorem_12_5_3_conclusion) ∧
  (type_of% @Polyfold.UntamedCorner.isScFredholmSectionFunctor_sec) ∧
  (type_of% @Polyfold.HalfSpaceBundle.theorem_12_5_3_loc_halfSpace) ∧
  (type_of% @Polyfold.EpStrongBundle.theorem_12_5_3_hyp.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.theorem_12_5_3_push.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.theorem_12_5_3_push_hyp.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.pullOrx_morIso_tgt.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.eqOn_morIso_of_functor.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.pullOrx_morIso_eq_orMor.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.germEq_morIso_sheet.{0}) ∧
  (type_of% @Polyfold.StrongBundle.LocalIso.isContOrOn_pullOrx.{0, 0, 0, 0}) ∧
  (type_of% @Polyfold.StrongBundle.LocalIso.orxVia_comm.{0, 0, 0, 0}) ∧
  (type_of% @Polyfold.StrongBundle.LocalIso.orxVia_comm_local.{0, 0, 0, 0}) ∧
  (type_of% @Polyfold.EpStrongBundle.theorem_12_5_3_iff_loc.{0}) ∧
  (type_of% @Polyfold.isOrientationTopology_iff_loc.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.theorem_12_5_3_loc.{0},
    @Polyfold.EpStrongBundle.theorem_12_5_3_push_loc.{0},
    @Polyfold.orProj_two_loc.{0, 0},
    @Polyfold.theorem_6_6_17_loc.{0, 0},
    @Polyfold.StrongBundle.Dom.transportLoc_eq.{0, 0},
    @Polyfold.orLocalTransportLoc_transport_eq.{0, 0},
    @Polyfold.StrongBundle.LocalIso.orLoc_comm.{0, 0, 0, 0},
    @Polyfold.StrongBundle.LocalIso.isContOn_pullLoc.{0, 0, 0, 0},
    @Polyfold.UntamedCorner.theorem_12_5_3_untamed_not,
    @Polyfold.UntamedCorner.not_theorem_12_5_3_conclusion,
    @Polyfold.UntamedCorner.isScFredholmSectionFunctor_sec,
    @Polyfold.HalfSpaceBundle.theorem_12_5_3_loc_halfSpace,
    @Polyfold.EpStrongBundle.theorem_12_5_3_hyp.{0},
    @Polyfold.EpStrongBundle.theorem_12_5_3_push.{0},
    @Polyfold.EpStrongBundle.theorem_12_5_3_push_hyp.{0},
    @Polyfold.EpStrongBundle.pullOrx_morIso_tgt.{0},
    @Polyfold.EpStrongBundle.eqOn_morIso_of_functor.{0},
    @Polyfold.EpStrongBundle.pullOrx_morIso_eq_orMor.{0},
    @Polyfold.EpStrongBundle.germEq_morIso_sheet.{0},
    @Polyfold.StrongBundle.LocalIso.isContOrOn_pullOrx.{0, 0, 0, 0},
    @Polyfold.StrongBundle.LocalIso.orxVia_comm.{0, 0, 0, 0},
    @Polyfold.StrongBundle.LocalIso.orxVia_comm_local.{0, 0, 0, 0},
    @Polyfold.EpStrongBundle.theorem_12_5_3_iff_loc.{0},
    @Polyfold.isOrientationTopology_iff_loc.{0, 0}⟩

/-- Clauses (1)–(3) of `B` (the local homeomorphism, two-point fibres, transport sections). -/
def B123 : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → Obj)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle X.PObj P)
    [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B)
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × Obj → Obj))]
    [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × (Fin n → ℝ) × Obj)]
    [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × Obj → Obj))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj) → (Fin n → ℝ) × Obj))]
    (hX : X.IsTame) (hbump : X.PObj.AdmitsBumpFunctions) (f : Obj → W)
    (hF : E.IsScFredholmSectionFunctor f) (hfT : B.IsScFredholmSectionTame f)
    (hsec : B.HasScPlusSectionsThrough),
    letI : TopologicalSpace (OrSpace f hF.2) := topO hX hbump hfT hsec hF.2
    IsLocalHomeomorph (orProj f hF.2) ∧
    (∀ x : X.PObj.SmoothLevel, (orProj f hF.2 ⁻¹' {x}).ncard = 2) ∧
    (∀ (x : Obj) (hx : x ∈ X.PObj.smoothSet) (ox : Orx f hF.2 x hx),
      ∃ (U : Set Obj) (o : (y : Obj) → (hy : y ∈ X.PObj.smoothSet) → Orx f hF.2 y hy),
        x ∈ U ∧ (orLocalTransport hX hbump hfT hsec).IsContOn U o ∧ o x hx = ox) ∧
    (∀ (U : Set Obj) (o : (y : Obj) → (hy : y ∈ X.PObj.smoothSet) → Orx f hF.2 y hy),
      (orLocalTransport hX hbump hfT hsec).IsContOn U o →
      IsContLocSec hF.2 inferInstance U (fun y => Sigma.mk y.1 (o y.1.1 y.1.2)))

theorem part123 (hhyp : type_of% @Polyfold.EpStrongBundle.theorem_12_5_3_hyp.{0}) : B123 := by
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ E _ _ _ _ hX hbump f hF hfT hsec
  let _ : TopologicalSpace (OrSpace f hF.2) := topO hX hbump hfT hsec hF.2
  refine ⟨isLocalHomeomorph_orProj _, fun x => ?_, fun x hx ox => ?_, fun U o ho => ?_⟩
  · obtain ⟨p, q, hpq, hp, hq, hall⟩ := (hhyp (B := B) hX hbump hfT).2 x
    have : orProj f hF.2 ⁻¹' {x} = {p, q} := by
      ext r
      refine ⟨fun hr => hall r hr, ?_⟩
      rintro (rfl | rfl)
      · exact hp
      · exact hq
    rw [this, Set.ncard_pair hpq]
  · obtain ⟨U, o, ho, -, hxU, hox⟩ := exists_isContOrOn (orLocalTransport hX hbump hfT hsec)
      (⟨⟨x, hx⟩, ox⟩ : OrSpace f hF.2)
    exact ⟨U, o, hxU, ho, hox.symm⟩
  · refine ⟨?_, fun y => rfl⟩
    have h := continuousOn_orSec (L := orLocalTransport hX hbump hfT hsec) ho
    exact h.domRestrict


/-- Partial `A → B`: clauses (1)–(3) of `B`, from A's conjunct `theorem_12_5_3_hyp`. -/
theorem A_to_B123 : A → B123 := fun hA => part123 hA.2.2.2.2.2.2.2.2.2.2.2.2.1

/-! The three banned names reached by `A_to_B123` (`transportLoc_eq`,
`isScFredholmSectionFunctor_sec`, `eqOn_morIso_of_functor`) are exactly those reached by the
statement `A` itself: they occur as proof arguments inside the types of A's conjuncts (e.g.
`E.eqOn_morIso_of_functor hF σ` in `theorem_12_5_3_push_hyp`).  The proof `part123`, which takes
only the conjunct `theorem_12_5_3_hyp` as hypothesis, passes the plain check. -/

def stmtA : Prop := A
def stmtB123 : Prop := B123

/--
error: rt_check FAIL: RoundTrip.V12_24.stmtA uses [Polyfold.StrongBundle.Dom.transportLoc_eq,
 Polyfold.UntamedCorner.isScFredholmSectionFunctor_sec,
 Polyfold.EpStrongBundle.eqOn_morIso_of_functor]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V12_24.stmtA [Polyfold.EpStrongBundle.theorem_12_5_3_loc,
  Polyfold.EpStrongBundle.theorem_12_5_3_push_loc,
  Polyfold.orProj_two_loc,
  Polyfold.theorem_6_6_17_loc,
  Polyfold.StrongBundle.Dom.transportLoc_eq,
  Polyfold.orLocalTransportLoc_transport_eq,
  Polyfold.StrongBundle.LocalIso.orLoc_comm,
  Polyfold.StrongBundle.LocalIso.isContOn_pullLoc,
  Polyfold.UntamedCorner.theorem_12_5_3_untamed_not,
  Polyfold.UntamedCorner.not_theorem_12_5_3_conclusion,
  Polyfold.UntamedCorner.isScFredholmSectionFunctor_sec,
  Polyfold.HalfSpaceBundle.theorem_12_5_3_loc_halfSpace,
  Polyfold.EpStrongBundle.theorem_12_5_3_hyp,
  Polyfold.EpStrongBundle.theorem_12_5_3_push,
  Polyfold.EpStrongBundle.theorem_12_5_3_push_hyp,
  Polyfold.EpStrongBundle.pullOrx_morIso_tgt,
  Polyfold.EpStrongBundle.eqOn_morIso_of_functor,
  Polyfold.EpStrongBundle.pullOrx_morIso_eq_orMor,
  Polyfold.EpStrongBundle.germEq_morIso_sheet,
  Polyfold.StrongBundle.LocalIso.isContOrOn_pullOrx,
  Polyfold.StrongBundle.LocalIso.orxVia_comm,
  Polyfold.StrongBundle.LocalIso.orxVia_comm_local,
  Polyfold.EpStrongBundle.theorem_12_5_3_iff_loc,
  Polyfold.isOrientationTopology_iff_loc]

#rt_check RoundTrip.V12_24.stmtB123 [Polyfold.EpStrongBundle.theorem_12_5_3_loc,
  Polyfold.EpStrongBundle.theorem_12_5_3_push_loc,
  Polyfold.orProj_two_loc,
  Polyfold.theorem_6_6_17_loc,
  Polyfold.StrongBundle.Dom.transportLoc_eq,
  Polyfold.orLocalTransportLoc_transport_eq,
  Polyfold.StrongBundle.LocalIso.orLoc_comm,
  Polyfold.StrongBundle.LocalIso.isContOn_pullLoc,
  Polyfold.UntamedCorner.theorem_12_5_3_untamed_not,
  Polyfold.UntamedCorner.not_theorem_12_5_3_conclusion,
  Polyfold.UntamedCorner.isScFredholmSectionFunctor_sec,
  Polyfold.HalfSpaceBundle.theorem_12_5_3_loc_halfSpace,
  Polyfold.EpStrongBundle.theorem_12_5_3_hyp,
  Polyfold.EpStrongBundle.theorem_12_5_3_push,
  Polyfold.EpStrongBundle.theorem_12_5_3_push_hyp,
  Polyfold.EpStrongBundle.pullOrx_morIso_tgt,
  Polyfold.EpStrongBundle.eqOn_morIso_of_functor,
  Polyfold.EpStrongBundle.pullOrx_morIso_eq_orMor,
  Polyfold.EpStrongBundle.germEq_morIso_sheet,
  Polyfold.StrongBundle.LocalIso.isContOrOn_pullOrx,
  Polyfold.StrongBundle.LocalIso.orxVia_comm,
  Polyfold.StrongBundle.LocalIso.orxVia_comm_local,
  Polyfold.EpStrongBundle.theorem_12_5_3_iff_loc,
  Polyfold.isOrientationTopology_iff_loc]

/--
error: rt_check FAIL: RoundTrip.V12_24.A_to_B123 uses [Polyfold.StrongBundle.Dom.transportLoc_eq,
 Polyfold.UntamedCorner.isScFredholmSectionFunctor_sec,
 Polyfold.EpStrongBundle.eqOn_morIso_of_functor]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V12_24.A_to_B123 [Polyfold.EpStrongBundle.theorem_12_5_3_loc,
  Polyfold.EpStrongBundle.theorem_12_5_3_push_loc,
  Polyfold.orProj_two_loc,
  Polyfold.theorem_6_6_17_loc,
  Polyfold.StrongBundle.Dom.transportLoc_eq,
  Polyfold.orLocalTransportLoc_transport_eq,
  Polyfold.StrongBundle.LocalIso.orLoc_comm,
  Polyfold.StrongBundle.LocalIso.isContOn_pullLoc,
  Polyfold.UntamedCorner.theorem_12_5_3_untamed_not,
  Polyfold.UntamedCorner.not_theorem_12_5_3_conclusion,
  Polyfold.UntamedCorner.isScFredholmSectionFunctor_sec,
  Polyfold.HalfSpaceBundle.theorem_12_5_3_loc_halfSpace,
  Polyfold.EpStrongBundle.theorem_12_5_3_hyp,
  Polyfold.EpStrongBundle.theorem_12_5_3_push,
  Polyfold.EpStrongBundle.theorem_12_5_3_push_hyp,
  Polyfold.EpStrongBundle.pullOrx_morIso_tgt,
  Polyfold.EpStrongBundle.eqOn_morIso_of_functor,
  Polyfold.EpStrongBundle.pullOrx_morIso_eq_orMor,
  Polyfold.EpStrongBundle.germEq_morIso_sheet,
  Polyfold.StrongBundle.LocalIso.isContOrOn_pullOrx,
  Polyfold.StrongBundle.LocalIso.orxVia_comm,
  Polyfold.StrongBundle.LocalIso.orxVia_comm_local,
  Polyfold.EpStrongBundle.theorem_12_5_3_iff_loc,
  Polyfold.isOrientationTopology_iff_loc]

/--
error: rt_check_soft FAIL: RoundTrip.V12_24.A_to_B123 uses [Polyfold.StrongBundle.Dom.transportLoc_eq,
 Polyfold.UntamedCorner.isScFredholmSectionFunctor_sec,
 Polyfold.EpStrongBundle.eqOn_morIso_of_functor]
-/
#guard_msgs (whitespace := lax) in
#rt_check_soft RoundTrip.V12_24.A_to_B123 [Polyfold.EpStrongBundle.theorem_12_5_3_loc,
  Polyfold.EpStrongBundle.theorem_12_5_3_push_loc,
  Polyfold.orProj_two_loc,
  Polyfold.theorem_6_6_17_loc,
  Polyfold.StrongBundle.Dom.transportLoc_eq,
  Polyfold.orLocalTransportLoc_transport_eq,
  Polyfold.StrongBundle.LocalIso.orLoc_comm,
  Polyfold.StrongBundle.LocalIso.isContOn_pullLoc,
  Polyfold.UntamedCorner.theorem_12_5_3_untamed_not,
  Polyfold.UntamedCorner.not_theorem_12_5_3_conclusion,
  Polyfold.UntamedCorner.isScFredholmSectionFunctor_sec,
  Polyfold.HalfSpaceBundle.theorem_12_5_3_loc_halfSpace,
  Polyfold.EpStrongBundle.theorem_12_5_3_hyp,
  Polyfold.EpStrongBundle.theorem_12_5_3_push,
  Polyfold.EpStrongBundle.theorem_12_5_3_push_hyp,
  Polyfold.EpStrongBundle.pullOrx_morIso_tgt,
  Polyfold.EpStrongBundle.eqOn_morIso_of_functor,
  Polyfold.EpStrongBundle.pullOrx_morIso_eq_orMor,
  Polyfold.EpStrongBundle.germEq_morIso_sheet,
  Polyfold.StrongBundle.LocalIso.isContOrOn_pullOrx,
  Polyfold.StrongBundle.LocalIso.orxVia_comm,
  Polyfold.StrongBundle.LocalIso.orxVia_comm_local,
  Polyfold.EpStrongBundle.theorem_12_5_3_iff_loc,
  Polyfold.isOrientationTopology_iff_loc]

#rt_check RoundTrip.V12_24.part123 [Polyfold.EpStrongBundle.theorem_12_5_3_loc,
  Polyfold.EpStrongBundle.theorem_12_5_3_push_loc,
  Polyfold.orProj_two_loc,
  Polyfold.theorem_6_6_17_loc,
  Polyfold.StrongBundle.Dom.transportLoc_eq,
  Polyfold.orLocalTransportLoc_transport_eq,
  Polyfold.StrongBundle.LocalIso.orLoc_comm,
  Polyfold.StrongBundle.LocalIso.isContOn_pullLoc,
  Polyfold.UntamedCorner.theorem_12_5_3_untamed_not,
  Polyfold.UntamedCorner.not_theorem_12_5_3_conclusion,
  Polyfold.UntamedCorner.isScFredholmSectionFunctor_sec,
  Polyfold.HalfSpaceBundle.theorem_12_5_3_loc_halfSpace,
  Polyfold.EpStrongBundle.theorem_12_5_3_hyp,
  Polyfold.EpStrongBundle.theorem_12_5_3_push,
  Polyfold.EpStrongBundle.theorem_12_5_3_push_hyp,
  Polyfold.EpStrongBundle.pullOrx_morIso_tgt,
  Polyfold.EpStrongBundle.eqOn_morIso_of_functor,
  Polyfold.EpStrongBundle.pullOrx_morIso_eq_orMor,
  Polyfold.EpStrongBundle.germEq_morIso_sheet,
  Polyfold.StrongBundle.LocalIso.isContOrOn_pullOrx,
  Polyfold.StrongBundle.LocalIso.orxVia_comm,
  Polyfold.StrongBundle.LocalIso.orxVia_comm_local,
  Polyfold.EpStrongBundle.theorem_12_5_3_iff_loc,
  Polyfold.isOrientationTopology_iff_loc]

#rt_overlap RoundTrip.V12_24.A_to_B123 [Polyfold.EpStrongBundle.theorem_12_5_3_loc,
  Polyfold.EpStrongBundle.theorem_12_5_3_push_loc,
  Polyfold.orProj_two_loc,
  Polyfold.theorem_6_6_17_loc,
  Polyfold.StrongBundle.Dom.transportLoc_eq,
  Polyfold.orLocalTransportLoc_transport_eq,
  Polyfold.StrongBundle.LocalIso.orLoc_comm,
  Polyfold.StrongBundle.LocalIso.isContOn_pullLoc,
  Polyfold.UntamedCorner.theorem_12_5_3_untamed_not,
  Polyfold.UntamedCorner.not_theorem_12_5_3_conclusion,
  Polyfold.UntamedCorner.isScFredholmSectionFunctor_sec,
  Polyfold.HalfSpaceBundle.theorem_12_5_3_loc_halfSpace,
  Polyfold.EpStrongBundle.theorem_12_5_3_hyp,
  Polyfold.EpStrongBundle.theorem_12_5_3_push,
  Polyfold.EpStrongBundle.theorem_12_5_3_push_hyp,
  Polyfold.EpStrongBundle.pullOrx_morIso_tgt,
  Polyfold.EpStrongBundle.eqOn_morIso_of_functor,
  Polyfold.EpStrongBundle.pullOrx_morIso_eq_orMor,
  Polyfold.EpStrongBundle.germEq_morIso_sheet,
  Polyfold.StrongBundle.LocalIso.isContOrOn_pullOrx,
  Polyfold.StrongBundle.LocalIso.orxVia_comm,
  Polyfold.StrongBundle.LocalIso.orxVia_comm_local,
  Polyfold.EpStrongBundle.theorem_12_5_3_iff_loc,
  Polyfold.isOrientationTopology_iff_loc]

end RoundTrip.V12_24
