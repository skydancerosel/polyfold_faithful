import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_3

/-! Round trip for V7_3 (Definition 7.3: ep-groupoids).

The listed definitions are `EpGroupoid`, `IsScSmoothComp`, `IsScSmoothCompSheet`; the listed
theorems are `isScSmoothComp_iff_sheet`, `EpGroupoid.isScSmoothCompSheet`,
`EpGroupoid.isScSmoothMap_src`, `EpGroupoid.isScSmoothMap_tgt` (one universe each) and
`MPolyfold.isSubMPolyfold_fibredProduct` (three universes); `A` is the conjunction of their
types, universes at `0`.

* `A → B`.  (a) Every project `EpGroupoid` is a text ep-groupoid: (1), (2) are fields; (3) the
  project's `IsProperMap` gives B's "continuous with compact preimages" (`IsProperMap.continuous`,
  `IsProperMap.isCompact_preimage`); (4) B's existential sub-M-polyfold structure of
  `𝐗 ₛ×ₜ 𝐗` is supplied by the hypothesis (Proposition 2.46 = conjunct 5 of `A`), with the
  project's paracompactness instances, and the field `isScSmoothComp` is then literally B's map
  (all the extra arguments are proofs of Props, so proof irrelevance identifies the two
  sub-M-polyfolds).  (b) Conversely a text ep-groupoid is an `EpGroupoid`: the only non-trivial
  step is B's properness `→ IsProperMap`, valid since `X` is metrizable
  (`MPolyfold.metrizableSpace`), hence compactly generated Hausdorff
  (`isProperMap_iff_isCompact_preimage`); (4) is again proof irrelevance.  (c) is conjunct 5 of
  `A` plus the paracompactness instances; (d) is conjuncts 3, 4 of `A`.
* `B → A`.  Conjuncts 3, 4 are B (d).  Conjuncts 1, 2, 5 are not about anything `B` speaks of
  (`B` never mentions the sheet form `IsScSmoothCompSheet`, and Proposition 2.46 is for arbitrary
  `f`, `g`, `X`, `Y`, `Z`, while B (c) is only for `s`, `t` of a groupoid); they are re-proved here
  outright, by the project's own route (the retraction `fibredSubDataL` and
  `isScDiffeoOn_snd_fibredProduct`). -/

namespace RoundTrip.V7_3
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.isScSmoothComp_iff_sheet.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isScSmoothCompSheet.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isScSmoothMap_src.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isScSmoothMap_tgt.{0}) ∧
  (type_of% @Polyfold.MPolyfold.isSubMPolyfold_fibredProduct.{0, 0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.isScSmoothComp_iff_sheet.{0}, @Polyfold.EpGroupoid.isScSmoothCompSheet.{0},
    @Polyfold.EpGroupoid.isScSmoothMap_src.{0}, @Polyfold.EpGroupoid.isScSmoothMap_tgt.{0},
    @Polyfold.MPolyfold.isSubMPolyfold_fibredProduct.{0, 0, 0}⟩

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _
  refine ⟨?_, ?_, ?_, fun X => ⟨hA.2.2.1 X, hA.2.2.2.1 X⟩⟩
  · -- (a)
    intro X
    refine ⟨X.isLocalScDiffeo_src, X.isLocalScDiffeo_tgt, X.isScSmoothMap_unit,
      X.isScSmoothMap_inv, fun x => ?_, ?_⟩
    · obtain ⟨V, hV, hxV, hp⟩ := X.exists_isProperMap x
      exact ⟨V, hV, hxV, hp.continuous, fun K hK => hp.isCompact_preimage hK⟩
    · let i1 := MPolyfold.paracompactSpace_prod X.PMor X.PMor
      let i2 := (X.PMor.prod X.PMor).paracompactSpace_subtype
        (MPolyfold.fibredProduct X.src X.tgt)
      exact ⟨i1, hA.2.2.2.2 X.isLocalScDiffeo_src (hA.2.2.2.1 X), i2, X.isScSmoothComp⟩
  · -- (b)
    intro G P Q h
    obtain ⟨hs, ht, hu, hi, hp, hm⟩ := h
    have hp' : ∀ x : Obj, ∃ V : Set Obj, IsOpen V ∧ x ∈ V ∧
        IsProperMap ((G.src ⁻¹' closure V).domRestrict G.tgt) := by
      intro x
      obtain ⟨V, hV, hxV, hc, hk⟩ := hp x
      have := P.metrizableSpace
      exact ⟨V, hV, hxV, isProperMap_iff_isCompact_preimage.2 ⟨hc, fun K hK => hk K hK⟩⟩
    obtain ⟨i1, hA', i2, hsm⟩ := hm
    refine ⟨{ G with
      PObj := P
      PMor := Q
      isLocalScDiffeo_src := hs
      isLocalScDiffeo_tgt := ht
      isScSmoothMap_unit := hu
      isScSmoothMap_inv := hi
      exists_isProperMap := hp'
      isScSmoothComp := hsm }, rfl, rfl, rfl⟩
  · -- (c)
    intro G P Q hs ht
    let i1 := MPolyfold.paracompactSpace_prod Q Q
    exact ⟨i1, hA.2.2.2.2 hs ht.isScSmoothMap,
      (Q.prod Q).paracompactSpace_subtype (MPolyfold.fibredProduct G.src G.tgt)⟩

/-! ### `B → A`: the conjuncts of `A` that `B` does not speak of, re-proved -/

section Reprove

universe u v w

/-- Proposition 2.46 (first statement), re-proved through the retraction `fibredSubDataL`. -/
theorem fibred_isSub {X : Type u} {Y : Type v} {Z : Type w} [TopologicalSpace X] [T2Space X]
    [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {P : MPolyfold X} {Q : MPolyfold Y}
    {S : MPolyfold Z} [ParacompactSpace (X × Y)] {f : X → Z} {g : Y → Z}
    (hf : P.IsLocalScDiffeo S f) (hg : Q.IsScSmoothMap S g) :
    (P.prod Q).IsSubMPolyfold (MPolyfold.fibredProduct f g) := by
  intro a haA
  obtain ⟨U, V, h, hx, hd⟩ := hf a.1
  have ha : a ∈ (MPolyfold.fibredSubDataL hd hg).V := ⟨hx, by
    change g a.2 ∈ V
    rw [← show f a.1 = g a.2 from haA]; exact hd.mapsTo hx⟩
  set d := MPolyfold.fibredSubDataL hd hg
  exact ⟨d.V, d.isOpen, ha, d.r, d.mapsTo, d.isScSmoothOn, d.idem, d.image⟩

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- Sc-smoothness on an open set is local. -/
theorem isScSmoothOn_of_local' {f : X → Y} {U : Set X} (hU : IsOpen U)
    (h : ∀ x ∈ U, ∃ W : Set X, x ∈ W ∧ P.IsScSmoothOn Q f W) : P.IsScSmoothOn Q f U := by
  have hcont : ContinuousOn f U := fun x hx => by
    obtain ⟨W, hxW, hW⟩ := h x hx
    exact (hW.continuousOn.continuousAt (hW.isOpen.mem_nhds hxW)).continuousWithinAt
  refine MPolyfold.IsScSmoothOn.of_exists_charts hU hcont fun x hx => ?_
  obtain ⟨W, hxW, hW⟩ := h x hx
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source x
  obtain ⟨ψ, hψ, hfx⟩ := Q.exists_isChart_mem_source (f x)
  have hVo : IsOpen ((W ∩ U ∩ φ.source) ∩ f ⁻¹' ψ.source) :=
    (hW.continuousOn.mono fun y hy => hy.1.1).isOpen_inter_preimage
      ((hW.isOpen.inter hU).inter φ.isOpen_source) ψ.isOpen_source
  exact ⟨φ, ψ, _, hφ, hψ, hVo, ⟨⟨⟨hxW, hx⟩, hxφ⟩, hfx⟩, fun y hy => ⟨hy.1.1.2, hy.1.2⟩,
    fun y hy => hy.2, hW.smooth φ ψ hφ hψ _ hVo (fun y hy => ⟨hy.1.1.1, hy.1.2⟩) fun y hy => hy.2⟩

end Reprove

section Reprove2

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- The literal condition (4) and its sheet form are equivalent, re-proved (the project's route,
with `fibred_isSub` in place of Proposition 2.46). -/
theorem comp_iff_sheet {PObj : MPolyfold Obj} {PMor : MPolyfold Mor}
    {src tgt : Mor → Obj} {comp : Mor → Mor → Mor} (hs : PMor.IsLocalScDiffeo PObj src)
    (ht : PMor.IsScSmoothMap PObj tgt) :
    IsScSmoothComp PObj PMor src tgt comp hs ht ↔ IsScSmoothCompSheet PObj PMor src tgt comp := by
  let _ := MPolyfold.paracompactSpace_prod PMor PMor
  let _ := (PMor.prod PMor).paracompactSpace_subtype (MPolyfold.fibredProduct src tgt)
  have hA := fibred_isSub hs ht
  have htc : Continuous tgt := continuousOn_univ.1 ht.continuousOn
  constructor
  · intro h σ W V hd
    have h' : (MPolyfold.subPolyfold hA).IsScSmoothMap PMor fun p => comp p.1.1 p.1.2 := h
    refine isScSmoothOn_of_local' (hd.isScSmoothOn_inv.isOpen.preimage htc) fun ψ hψ => ?_
    let a₀ : MPolyfold.fibredProduct src tgt := ⟨(σ (tgt ψ), ψ), hd.right_inv _ hψ⟩
    have hD := MPolyfold.isScDiffeoOn_snd_fibredProduct hA hd ht a₀
    refine ⟨tgt ⁻¹' V, hψ, ?_⟩
    refine (MPolyfold.IsScSmoothOn.comp h' hD.isScSmoothOn_inv (mapsTo_univ _ _)).congr
      fun y hy => ?_
    simp only [Function.comp_apply]
    rw [(MPolyfold.fibredSubDataL hd ht).retractInto_val a₀ ⟨hd.mapsTo_inv hy, hy⟩]
    rfl
  · intro h
    change (MPolyfold.subPolyfold hA).IsScSmoothMap PMor _
    refine isScSmoothOn_of_local' isOpen_univ fun a _ => ?_
    have ha : src a.1.1 = tgt a.1.2 := a.2
    obtain ⟨W, V, σ, haW, hd⟩ := hs a.1.1
    have hD := MPolyfold.isScDiffeoOn_snd_fibredProduct hA hd ht a
    refine ⟨Subtype.val ⁻¹' (W ×ˢ (tgt ⁻¹' V)), ⟨haW, ?_⟩, ?_⟩
    · change tgt a.1.2 ∈ V
      rw [← ha]
      exact hd.mapsTo haW
    · refine (MPolyfold.IsScSmoothOn.comp (h σ W V hd) hD.isScSmoothOn
        fun b hb => hb.2).congr fun b hb => ?_
      have hb' : src b.1.1 = tgt b.1.2 := b.2
      simp only [Function.comp_apply]
      rw [← hb', hd.left_inv _ hb.1]

end Reprove2

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun hs ht => comp_iff_sheet hs ht, fun X => ?_, fun {Obj Mor} _ _ _ _ _ _ X =>
    ((hB Obj Mor).2.2.2 X).1, fun {Obj Mor} _ _ _ _ _ _ X => ((hB Obj Mor).2.2.2 X).2,
    fun hf hg => fibred_isSub hf hg⟩
  exact (comp_iff_sheet _ _).1 X.isScSmoothComp

/- `#rt_check` fails only because `IsScSmoothComp` (a definition, the statement of condition (4))
mentions Proposition 2.46 in its abstracted proof argument `IsScSmoothComp._proof_3`; no proof
here uses `isSubMPolyfold_fibredProduct` otherwise (`B_to_A` uses the re-proof `fibred_isSub`). -/
#rt_check_soft RoundTrip.V7_3.A_to_B [Polyfold.isScSmoothComp_iff_sheet, Polyfold.EpGroupoid.isScSmoothCompSheet, Polyfold.EpGroupoid.isScSmoothMap_src, Polyfold.EpGroupoid.isScSmoothMap_tgt, Polyfold.MPolyfold.isSubMPolyfold_fibredProduct]
#rt_check_soft RoundTrip.V7_3.B_to_A [Polyfold.isScSmoothComp_iff_sheet, Polyfold.EpGroupoid.isScSmoothCompSheet, Polyfold.EpGroupoid.isScSmoothMap_src, Polyfold.EpGroupoid.isScSmoothMap_tgt, Polyfold.MPolyfold.isSubMPolyfold_fibredProduct]
#rt_overlap RoundTrip.V7_3.B_to_A [Polyfold.isScSmoothComp_iff_sheet, Polyfold.EpGroupoid.isScSmoothCompSheet, Polyfold.EpGroupoid.isScSmoothMap_src, Polyfold.EpGroupoid.isScSmoothMap_tgt, Polyfold.MPolyfold.isSubMPolyfold_fibredProduct]

end RoundTrip.V7_3
