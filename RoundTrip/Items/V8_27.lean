import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_27

/-! Round trip for V8_27 (Definition 8.5.1 = 2017 Definition 8.8: proper covering functors).

The item lists the definitions `EpFunctor.IsProperCovering`, `EpFunctor.fibredMap` (vocabulary)
and two theorems; `A` is the conjunction of their types, universes at `0`:
`MPolyfold.isSubMPolyfold_fibredProduct` (Part I's Proposition 2.46: for a local
sc-diffeomorphism `f` and an sc-smooth `g`, `X ₓ×_g Y` is a sub-M-polyfold of `X × Y`; listed
because condition (3) of the definition uses it) and `EpFunctor.isProperCovering_id`.

`B`: `F.IsProperCovering ↔ IsProperCoveringB F` (B's literal reading).

* `A_to_B`: the two definitions agree up to repackaging: in (2) B asks `U(y)` open (it is the
  domain of an sc-diffeomorphism) and an inverse for each `y` (the project gives a family `σ`;
  conversely we choose one); in (3) B quantifies existentially over the paracompactness
  instances and the sub-M-polyfold proof, and `subPolyfold` does not depend on the proof (proof
  irrelevance).  The project's (3) is stated with the proof
  `isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src F.isScSmoothMap_obj`; we supply the
  witness from `A`'s first conjunct instead.
* `B_to_A`: `isProperCovering_id` from the backward half of `B`, proving `IsProperCoveringB` of
  the identity (one sheet; `φ ↦ (φ, s φ)` with inverse `(φ, x) ↦ φ`).  Proposition 2.46 is not a
  consequence of `B` (a general statement about M-polyfolds); it is re-proved outright (the
  project's proof, copied: `fibredSubDataL`), as is the private helper
  `isScSmoothOn_subPolyfold_of_val` of `NonVacuityBundle.lean`. -/

namespace RoundTrip.V8_27
open Polyfold Set Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.isSubMPolyfold_fibredProduct.{0, 0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.isProperCovering_id.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.isSubMPolyfold_fibredProduct.{0, 0, 0},
    @Polyfold.EpFunctor.isProperCovering_id.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨hA1, -⟩
  intro ObjY MorY _ _ _ _ _ _ ObjX MorX _ _ _ _ _ _ Y X F
  let _ := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
  let _ := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
  have hA : (X.PMor.prod Y.PObj).IsSubMPolyfold (MPolyfold.fibredProduct X.src F.obj) :=
    hA1 X.isLocalScDiffeo_src F.isScSmoothMap_obj
  constructor
  · intro h
    have h3 : ∃ g : MPolyfold.fibredProduct X.src F.obj → MorY,
        Y.PMor.IsScDiffeoOn ((X.PMor.prod Y.PObj).subPolyfold hA) (LB F) g univ univ :=
      h.isScDiffeo_fibredMap
    refine ⟨h.surjective, h.isLocalScDiffeo, fun x => ⟨h.finite_fiber x, ?_⟩, ⟨_, hA, _, h3⟩⟩
    obtain ⟨U, V, σ, hU, hx, hdisj, hV, hpre⟩ := h.evenlyCovered x
    exact ⟨U, V, hU, hx, fun y hy => ⟨(hV y hy).2.isScSmoothOn.isOpen, (hV y hy).1, σ y,
      (hV y hy).2⟩, hdisj, hpre⟩
  · rintro ⟨h1, h2, h3, i1, hA', i2, g, hg⟩
    have h4 : ∃ g : MPolyfold.fibredProduct X.src F.obj → MorY,
        Y.PMor.IsScDiffeoOn ((X.PMor.prod Y.PObj).subPolyfold hA) (LB F) g univ univ :=
      ⟨g, hg⟩
    refine ⟨h1, h2, fun x => (h3 x).1, fun x => ?_, h4⟩
    classical
    obtain ⟨U, V, hU, hx, hV, hdisj, hpre⟩ := (h3 x).2
    refine ⟨U, V, fun y => if hy : y ∈ F.obj ⁻¹' {x} then Classical.choose (hV y hy).2.2
      else fun _ => y, hU, hx, hdisj, fun y hy => ⟨(hV y hy).2.1, ?_⟩, hpre⟩
    dsimp only
    rw [dif_pos hy]
    exact Classical.choose_spec (hV y hy).2.2

/-! ### Re-proved outright: Proposition 2.46 and the private helper (the project's proofs) -/

section Reproved

variable {X Y Z : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
  [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] [TopologicalSpace Z] [T2Space Z]
  [ParacompactSpace Z]

theorem isSubMPolyfold_fibredProduct' {P : MPolyfold X} {Q : MPolyfold Y} {S : MPolyfold Z}
    [ParacompactSpace (X × Y)] {f : X → Z} {g : Y → Z} (hf : P.IsLocalScDiffeo S f)
    (hg : Q.IsScSmoothMap S g) : (P.prod Q).IsSubMPolyfold (MPolyfold.fibredProduct f g) := by
  intro a ha
  obtain ⟨U, V, h, hx, hd⟩ := hf a.1
  have ha' : a ∈ (MPolyfold.fibredSubDataL hd hg).V := ⟨hx, by
    change g a.2 ∈ V
    rw [← show f a.1 = g a.2 from ha]; exact hd.mapsTo hx⟩
  set d := MPolyfold.fibredSubDataL hd hg
  exact ⟨d.V, d.isOpen, ha', d.r, d.mapsTo, d.isScSmoothOn, d.idem, d.image⟩

theorem isScSmoothOn_subPolyfold_of_val' {P : MPolyfold X} {Q : MPolyfold Y} {A : Set Y}
    (hA : Q.IsSubMPolyfold A) [ParacompactSpace A] {f : X → A} {U : Set X}
    (hf : P.IsScSmoothOn Q (fun x => (f x : Y)) U) :
    P.IsScSmoothOn (MPolyfold.subPolyfold hA) f U := by
  refine MPolyfold.IsScSmoothOn.of_locally hf.isOpen fun x hx => ?_
  set d := hA.data (f x).2
  have hU' : IsOpen (U ∩ (fun x => (f x : Y)) ⁻¹' d.V) :=
    hf.continuousOn.isOpen_inter_preimage hf.isOpen d.isOpen
  refine ⟨_, hU', ⟨hx, hA.mem_data_V (f x).2⟩, inter_subset_left, ?_⟩
  refine (MPolyfold.IsScSmoothOn.comp (MPolyfold.subPolyfold_retraction_isScSmooth hA d (f x))
    (hf.mono hU' inter_subset_left) fun y hy => hy.2).congr fun y hy => Subtype.ext ?_
  simp only [Function.comp_apply]
  rw [d.retractInto_val (f x) hy.2]
  exact d.apply_eq_self ⟨(f y).2, hy.2⟩

end Reproved

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_⟩
  · intros
    exact isSubMPolyfold_fibredProduct' ‹_› ‹_›
  · intro Obj Mor _ _ _ _ _ _ X
    refine (hB Obj Mor Obj Mor X X (EpFunctor.id X)).2
      ⟨surjective_id, fun x => ⟨univ, univ, fun y => y, mem_univ x,
        MPolyfold.isScDiffeoOn_id isOpen_univ⟩, fun x => ⟨finite_singleton x, ?_⟩, ?_⟩
    · refine ⟨univ, fun _ => univ, isOpen_univ, mem_univ x, fun y _ => ⟨isOpen_univ, mem_univ y,
        fun y => y, MPolyfold.isScDiffeoOn_id isOpen_univ⟩, ?_, ?_⟩
      · change ({x} : Set Obj).PairwiseDisjoint _
        exact pairwiseDisjoint_singleton _ _
      · change univ = ⋃ y ∈ ({x} : Set Obj), univ
        rw [biUnion_singleton]
    · let _ := MPolyfold.paracompactSpace_prod X.PMor X.PObj
      have hA : (X.PMor.prod X.PObj).IsSubMPolyfold
          (MPolyfold.fibredProduct X.src (EpFunctor.id X).obj) :=
        isSubMPolyfold_fibredProduct' X.isLocalScDiffeo_src (EpFunctor.id X).isScSmoothMap_obj
      let _ := (X.PMor.prod X.PObj).paracompactSpace_subtype
        (MPolyfold.fibredProduct X.src (EpFunctor.id X).obj)
      exact ⟨_, hA, _, fun p => (p : Mor × Obj).1,
        { isScSmoothOn := isScSmoothOn_subPolyfold_of_val' _
            (MPolyfold.IsScSmoothOn.prodMk MPolyfold.isScSmoothMap_id X.isScSmoothMap_src)
          isScSmoothOn_inv := (MPolyfold.isScSmoothMap_fst X.PMor X.PObj).comp
            (MPolyfold.subPolyfold_inclusion_isScSmooth _)
          mapsTo := mapsTo_univ _ _
          mapsTo_inv := mapsTo_univ _ _
          left_inv := fun _ _ => rfl
          right_inv := fun p _ => Subtype.ext (Prod.ext rfl p.2) }⟩

/-! ### Harness checks

The structure `EpFunctor.IsProperCovering` states its condition (3) with the proof
`MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src F.isScSmoothMap_obj` (a banned
theorem of this item) inside the type of its field `isScDiffeo_fibredMap`, hence inside the
types of the structure's constructor, projection and recursors.  `A_to_B` must destructure and
build `IsProperCovering`, so plain `#rt_check` reaches the banned theorem through those types
(recorded with `#guard_msgs`), although the proof never uses it: the sub-M-polyfold witness is
taken from `A`'s first conjunct, and the field values are transported to it by proof
irrelevance.  `#rt_check_except_struct` is the harness traversal `rtCollect` with the
auto-generated constants of `IsProperCovering` (`mk`, `rec`, `casesOn`, `recOn`,
`isScDiffeo_fibredMap`) not followed.  `B_to_A` passes the plain check. -/

open Lean Elab Command in
/-- `#rt_check_except_struct T [nᵢ]`: the proof of `T` reaches the banned `nᵢ` only through the
types of the auto-generated constants of the structure `EpFunctor.IsProperCovering`. -/
elab "#rt_check_except_struct " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let skip : NameSet := [``Polyfold.EpFunctor.IsProperCovering.mk,
    ``Polyfold.EpFunctor.IsProperCovering.rec, ``Polyfold.EpFunctor.IsProperCovering.casesOn,
    ``Polyfold.EpFunctor.IsProperCovering.recOn,
    ``Polyfold.EpFunctor.IsProperCovering.isScDiffeo_fibredMap].foldl NameSet.insert {}
  let used := rtCollect env roots.toList skip
  if used.contains ``sorryAx then throwError "FAIL: {t.getId} contains sorry"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  unless bad.isEmpty do
    throwError "FAIL: {t.getId} uses {bad} outside the structure constants of IsProperCovering"
  logInfo m!"OK: {t.getId} reaches the banned theorems only through the types of the structure constants of IsProperCovering"

/--
error: rt_check FAIL: RoundTrip.V8_27.A_to_B uses [Polyfold.MPolyfold.isSubMPolyfold_fibredProduct]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V8_27.A_to_B [Polyfold.MPolyfold.isSubMPolyfold_fibredProduct,
  Polyfold.EpFunctor.isProperCovering_id]
#rt_check_except_struct RoundTrip.V8_27.A_to_B [Polyfold.MPolyfold.isSubMPolyfold_fibredProduct,
  Polyfold.EpFunctor.isProperCovering_id]
#rt_check RoundTrip.V8_27.B_to_A [Polyfold.MPolyfold.isSubMPolyfold_fibredProduct,
  Polyfold.EpFunctor.isProperCovering_id]
#rt_overlap RoundTrip.V8_27.B_to_A [Polyfold.MPolyfold.isSubMPolyfold_fibredProduct,
  Polyfold.EpFunctor.isProperCovering_id]

end RoundTrip.V8_27
