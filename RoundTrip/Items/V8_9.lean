import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_9

/-! Round trip for V8_9 (Lemma 8.1.7 (2017: 8.6): the structure maps of `T(X, 𝐗)`).

`A` is the conjunction of the types of the ten listed theorems, universes instantiated at `0`
(`B` lives in `Type`).  Nine are about the tangent `T(X, 𝐗)`; `isScSmoothComp_iff_sheet` is
Chapter 7's general equivalence of condition (4) of Definition 7.3 with its sheet form.

* Notions: `B`'s `tangentMap hs`, `tangentMap ht`, `tangentMap hι` are the project's `tSrc`,
  `tTgt`, `tInv` (proof irrelevance), `tCompB X hs` is `tComp`, and `B`'s `IsScSmoothMulOnB` is
  the project's `IsScSmoothComp` up to the (proof-irrelevant) paracompactness instances and
  sub-M-polyfold proof, which `B` quantifies existentially.  `B`'s unit clause (some `u_T` with
  `IsTUnitB`, and every such map sc-smooth) matches `tUnit` by `tBase_tUnit`, `tSrc_tUnit`,
  `tangent_ext`.
* `B_to_A`: all tangent conjuncts come from `B`; the sheet form `isScSmoothCompSheet_tangent`
  comes from `B`'s literal condition (4) through `iffSheet`, a copy of the project's proof of
  `isScSmoothComp_iff_sheet` (with `IsScSmoothOn.of_locally` in place of a private helper), which
  also proves that conjunct outright: it is a general Chapter 7 lemma about which `B` says
  nothing.
* **Harness.** The statements of `isScSmoothComp_tangent` and `lemma_8_1_7` mention the banned
  theorems `isLocalScDiffeo_tSrc`, `isLocalScDiffeo_tTgt` as proof arguments of
  `IsScSmoothComp`, so every term mentioning `A` reaches them.  `A'` is `A` with those two proof
  arguments replaced by non-banned proofs of the same propositions; `A` and `A'` are
  definitionally equal (proof irrelevance), and `A_to_B`, `B_to_A` are proved through `A'`
  (`A'_to_B`, `B_to_A'`) and stated with `A`. -/

namespace RoundTrip.V8_9
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.isLocalScDiffeo_tSrc.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isLocalScDiffeo_tTgt.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.surjective_tSrc.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.surjective_tTgt.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isScSmoothMap_tUnit.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isScSmoothMap_tInv.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isScSmoothCompSheet_tangent.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isScSmoothComp_tangent.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.lemma_8_1_7.{0}) ∧
  (type_of% @Polyfold.isScSmoothComp_iff_sheet.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.isLocalScDiffeo_tSrc.{0}, @Polyfold.EpGroupoid.isLocalScDiffeo_tTgt.{0},
    @Polyfold.EpGroupoid.surjective_tSrc.{0}, @Polyfold.EpGroupoid.surjective_tTgt.{0},
    @Polyfold.EpGroupoid.isScSmoothMap_tUnit.{0}, @Polyfold.EpGroupoid.isScSmoothMap_tInv.{0},
    @Polyfold.EpGroupoid.isScSmoothCompSheet_tangent.{0},
    @Polyfold.EpGroupoid.isScSmoothComp_tangent.{0}, @Polyfold.EpGroupoid.lemma_8_1_7.{0},
    @Polyfold.isScSmoothComp_iff_sheet.{0}⟩

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `Ts` is a local sc-diffeomorphism (the body of the banned `isLocalScDiffeo_tSrc`, used only
as a proof argument inside statements). -/
theorem lsd_tSrc (X : EpGroupoid Obj Mor) :
    X.PMor.tangentPolyfold.IsLocalScDiffeo X.PObj.tangentPolyfold X.tSrc :=
  X.isLocalScDiffeo_src.tangentMap

/-- `Tt` is sc-smooth (a proof argument inside statements). -/
theorem sm_tTgt (X : EpGroupoid Obj Mor) :
    X.PMor.tangentPolyfold.IsScSmoothMap X.PObj.tangentPolyfold X.tTgt :=
  X.isLocalScDiffeo_tgt.tangentMap.isScSmoothMap

end

/-- `A` with the proof arguments `isLocalScDiffeo_tSrc`, `isLocalScDiffeo_tTgt.isScSmoothMap` of
`IsScSmoothComp` replaced by `lsd_tSrc`, `sm_tTgt` (definitionally equal to `A`). -/
def A' : Prop :=
  (type_of% @Polyfold.EpGroupoid.isLocalScDiffeo_tSrc.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isLocalScDiffeo_tTgt.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.surjective_tSrc.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.surjective_tTgt.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isScSmoothMap_tUnit.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isScSmoothMap_tInv.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isScSmoothCompSheet_tangent.{0}) ∧
  (∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    IsScSmoothComp X.PObj.tangentPolyfold X.PMor.tangentPolyfold X.tSrc X.tTgt X.tComp
      (lsd_tSrc X) (sm_tTgt X)) ∧
  (∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    X.PMor.tangentPolyfold.IsLocalScDiffeo X.PObj.tangentPolyfold X.tSrc ∧
      Function.Surjective X.tSrc ∧
      X.PMor.tangentPolyfold.IsLocalScDiffeo X.PObj.tangentPolyfold X.tTgt ∧
      Function.Surjective X.tTgt ∧
      X.PObj.tangentPolyfold.IsScSmoothMap X.PMor.tangentPolyfold X.tUnit ∧
      X.PMor.tangentPolyfold.IsScSmoothMap X.PMor.tangentPolyfold X.tInv ∧
      IsScSmoothComp X.PObj.tangentPolyfold X.PMor.tangentPolyfold X.tSrc X.tTgt X.tComp
        (lsd_tSrc X) (sm_tTgt X) ∧
      IsScSmoothCompSheet X.PObj.tangentPolyfold X.PMor.tangentPolyfold X.tSrc X.tTgt
        X.tComp) ∧
  (type_of% @Polyfold.isScSmoothComp_iff_sheet.{0})

/-! ### Glue -/

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

theorem isTUnitB_tUnit (X : EpGroupoid Obj Mor) (q : X.PObj.TangentSpace) :
    IsTUnitB X X.isScSmoothMap_src q (X.tUnit q) :=
  ⟨X.tBase_tUnit q, X.tSrc_tUnit q⟩

theorem eq_tUnit_of_isTUnitB (X : EpGroupoid Obj Mor) {q : X.PObj.TangentSpace}
    {v : X.PMor.TangentSpace} (hv : IsTUnitB X X.isScSmoothMap_src q v) : X.tUnit q = v :=
  X.tangent_ext ((X.tBase_tUnit q).trans hv.1.symm) ((X.tSrc_tUnit q).trans hv.2.symm)

end

/-- A copy of the project's proof of `isScSmoothComp_iff_sheet` (Chapter 7), with
`IsScSmoothOn.of_locally` in place of the private helper; no banned theorem is used. -/
theorem iffSheet.{u} {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {PObj : MPolyfold Obj}
    {PMor : MPolyfold Mor} {src tgt : Mor → Obj} {comp : Mor → Mor → Mor}
    (hs : PMor.IsLocalScDiffeo PObj src) (ht : PMor.IsScSmoothMap PObj tgt) :
    IsScSmoothComp PObj PMor src tgt comp hs ht ↔ IsScSmoothCompSheet PObj PMor src tgt comp := by
  let _ := MPolyfold.paracompactSpace_prod PMor PMor
  let _ := (PMor.prod PMor).paracompactSpace_subtype (MPolyfold.fibredProduct src tgt)
  have hA := MPolyfold.isSubMPolyfold_fibredProduct hs ht
  have htc : Continuous tgt := continuousOn_univ.1 ht.continuousOn
  constructor
  · intro h σ W V hd
    have h' : (MPolyfold.subPolyfold hA).IsScSmoothMap PMor fun p => comp p.1.1 p.1.2 := h
    have hUo : IsOpen (tgt ⁻¹' V) := hd.isScSmoothOn_inv.isOpen.preimage htc
    refine MPolyfold.IsScSmoothOn.of_locally hUo fun ψ hψ => ?_
    let a₀ : MPolyfold.fibredProduct src tgt := ⟨(σ (tgt ψ), ψ), hd.right_inv _ hψ⟩
    have hD := MPolyfold.isScDiffeoOn_snd_fibredProduct hA hd ht a₀
    refine ⟨tgt ⁻¹' V, hUo, hψ, subset_rfl, ?_⟩
    refine (MPolyfold.IsScSmoothOn.comp h' hD.isScSmoothOn_inv (Set.mapsTo_univ _ _)).congr
      fun y hy => ?_
    simp only [Function.comp_apply]
    rw [(MPolyfold.fibredSubDataL hd ht).retractInto_val a₀ ⟨hd.mapsTo_inv hy, hy⟩]
    rfl
  · intro h
    change (MPolyfold.subPolyfold hA).IsScSmoothMap PMor _
    refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun a _ => ?_
    have ha : src a.1.1 = tgt a.1.2 := a.2
    obtain ⟨W, V, σ, haW, hd⟩ := hs a.1.1
    have hD := MPolyfold.isScDiffeoOn_snd_fibredProduct hA hd ht a
    have hsm := (MPolyfold.IsScSmoothOn.comp (h σ W V hd) hD.isScSmoothOn fun b hb => hb.2)
    refine ⟨Subtype.val ⁻¹' (W ×ˢ (tgt ⁻¹' V)), hsm.isOpen, ⟨haW, ?_⟩, Set.subset_univ _, ?_⟩
    · change tgt a.1.2 ∈ V
      rw [← ha]
      exact hd.mapsTo haW
    · refine hsm.congr fun b hb => ?_
      have hb' : src b.1.1 = tgt b.1.2 := b.2
      simp only [Function.comp_apply]
      rw [← hb', hd.left_inv _ hb.1]

/-! ### The two directions -/

theorem A'_to_B : A' → B := by
  intro hA Obj Mor _ _ _ _ _ _ X
  obtain ⟨-, -, -, -, -, -, -, -, h6, -⟩ := hA
  obtain ⟨hls, hss, hlt, hst, hu, hi, hc, -⟩ := h6 X
  refine ⟨X.isScSmoothMap_src, X.isScSmoothMap_tgt, X.isScSmoothMap_inv, hss, hst, hls, hlt,
    hls.isScSmoothMap, hlt.isScSmoothMap, ⟨X.tUnit, isTUnitB_tUnit X⟩, fun uT huT => ?_, hi, ?_⟩
  · have : uT = X.tUnit := funext fun a => (eq_tUnit_of_isTUnitB X (huT a)).symm
    rw [this]
    exact hu
  · let _ := MPolyfold.paracompactSpace_prod X.PMor.tangentPolyfold X.PMor.tangentPolyfold
    let _ := (X.PMor.tangentPolyfold.prod X.PMor.tangentPolyfold).paracompactSpace_subtype
      (MPolyfold.fibredProduct (MPolyfold.tangentMap X.isScSmoothMap_src)
        (MPolyfold.tangentMap X.isScSmoothMap_tgt))
    exact ⟨inferInstance, MPolyfold.isSubMPolyfold_fibredProduct (lsd_tSrc X) (sm_tTgt X),
      inferInstance, hc⟩

theorem B_to_A' : B → A' := by
  intro hB
  have key : ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
      X.PMor.tangentPolyfold.IsLocalScDiffeo X.PObj.tangentPolyfold X.tSrc ∧
      Function.Surjective X.tSrc ∧
      X.PMor.tangentPolyfold.IsLocalScDiffeo X.PObj.tangentPolyfold X.tTgt ∧
      Function.Surjective X.tTgt ∧
      X.PObj.tangentPolyfold.IsScSmoothMap X.PMor.tangentPolyfold X.tUnit ∧
      X.PMor.tangentPolyfold.IsScSmoothMap X.PMor.tangentPolyfold X.tInv ∧
      IsScSmoothComp X.PObj.tangentPolyfold X.PMor.tangentPolyfold X.tSrc X.tTgt X.tComp
        (lsd_tSrc X) (sm_tTgt X) ∧
      IsScSmoothCompSheet X.PObj.tangentPolyfold X.PMor.tangentPolyfold X.tSrc X.tTgt
        X.tComp := by
    intro Obj Mor _ _ _ _ _ _ X
    obtain ⟨hs, ht, hι, hss, hst, hls, hlt, -, -, -, hu, hi, ⟨_, hA, _, hm⟩⟩ := hB Obj Mor X
    have hc : IsScSmoothComp X.PObj.tangentPolyfold X.PMor.tangentPolyfold X.tSrc X.tTgt X.tComp
        (lsd_tSrc X) (sm_tTgt X) := hm
    exact ⟨hls, hss, hlt, hst, hu X.tUnit (isTUnitB_tUnit X), hi, hc, (iffSheet _ _).1 hc⟩
  exact ⟨fun X => (key _ _ X).1, fun X => (key _ _ X).2.2.1, fun X => (key _ _ X).2.1,
    fun X => (key _ _ X).2.2.2.1, fun X => (key _ _ X).2.2.2.2.1,
    fun X => (key _ _ X).2.2.2.2.2.1, fun X => (key _ _ X).2.2.2.2.2.2.2,
    fun X => (key _ _ X).2.2.2.2.2.2.1, fun X => key _ _ X, fun hs ht => iffSheet hs ht⟩

theorem A_to_B : A → B := A'_to_B

theorem B_to_A : B → A := B_to_A'

#rt_check RoundTrip.V8_9.A_to_B [Polyfold.EpGroupoid.isLocalScDiffeo_tSrc,
  Polyfold.EpGroupoid.isLocalScDiffeo_tTgt, Polyfold.EpGroupoid.surjective_tSrc,
  Polyfold.EpGroupoid.surjective_tTgt, Polyfold.EpGroupoid.isScSmoothMap_tUnit,
  Polyfold.EpGroupoid.isScSmoothMap_tInv, Polyfold.EpGroupoid.isScSmoothCompSheet_tangent,
  Polyfold.EpGroupoid.isScSmoothComp_tangent, Polyfold.EpGroupoid.lemma_8_1_7,
  Polyfold.isScSmoothComp_iff_sheet]
#rt_check RoundTrip.V8_9.B_to_A [Polyfold.EpGroupoid.isLocalScDiffeo_tSrc,
  Polyfold.EpGroupoid.isLocalScDiffeo_tTgt, Polyfold.EpGroupoid.surjective_tSrc,
  Polyfold.EpGroupoid.surjective_tTgt, Polyfold.EpGroupoid.isScSmoothMap_tUnit,
  Polyfold.EpGroupoid.isScSmoothMap_tInv, Polyfold.EpGroupoid.isScSmoothCompSheet_tangent,
  Polyfold.EpGroupoid.isScSmoothComp_tangent, Polyfold.EpGroupoid.lemma_8_1_7,
  Polyfold.isScSmoothComp_iff_sheet]
#rt_overlap RoundTrip.V8_9.B_to_A [Polyfold.EpGroupoid.isLocalScDiffeo_tSrc,
  Polyfold.EpGroupoid.isLocalScDiffeo_tTgt, Polyfold.EpGroupoid.surjective_tSrc,
  Polyfold.EpGroupoid.surjective_tTgt, Polyfold.EpGroupoid.isScSmoothMap_tUnit,
  Polyfold.EpGroupoid.isScSmoothMap_tInv, Polyfold.EpGroupoid.isScSmoothCompSheet_tangent,
  Polyfold.EpGroupoid.isScSmoothComp_tangent, Polyfold.EpGroupoid.lemma_8_1_7,
  Polyfold.isScSmoothComp_iff_sheet]

end RoundTrip.V8_9
