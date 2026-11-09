import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_37

set_option maxSynthPendingDepth 3

/-! Round trip for V8_37 (Definition 8.5.9 / 2017: Definition 8.10: proper strong bundle covering
functors).

The item lists the definitions `StrongBundle.IsStrongBundleIsoOn`, `IsStrongBundleIsoOn.fiberEquiv`,
`EpFunctor.fibredSnd`, `EpStrongBundle.fibredLift`, `fibredBundleEquiv`,
`EpStrongBundle.IsProperStrongBundleCovering` (vocabulary) and five theorems; `A` is the
conjunction of their types, universes at `0`: `EpFunctor.isScSmoothMap_fibredSnd`
(`pr₂ : 𝐗 ₛ×_F Y → Y` is sc-smooth), the two `rfl` lemmas `pullbackProj_fibredBundleEquiv`,
`fibredBundleEquiv_symm_fibredLift` (the text's `𝐕 ₛ×_A W` read as a pull-back), and the
non-vacuity results `isProperStrongBundleCovering_id` (the identity of any strong bundle) and
`TrivialBundle.epBundle_isProperStrongBundleCovering` (the identity of `ℝⁿ × ℝᵏ → ℝⁿ`).

`B` is the definition comparison: B's transcription `IsPSBCoveringB EW EV F A` holds iff `A` is
the object map of a functor with the project's `IsProperStrongBundleCovering`.

* `A ⇒ B` (`B` is proved; of `A` only `isScSmoothMap_fibredSnd` is used, for the smoothness of
  `pr₂` that B's condition (3) quantifies over).  The two definitions agree:
  - "strong bundle map `A` with `Q ∘ A = F ∘ P`" (B: the project's `IsMap`, Definition 8.3.2)
    vs. the project's strong bundle functor (Definition 8.3.3): the non-item
    `IsMap.liftFunctor`, `isStrongBundleFunctor_liftFunctor` and `IsStrongBundleFunctor.isMap`;
  - B asks `U` open in the local isomorphisms and `U(y)` open in (2), and `F⁻¹(x)` finite; the
    project does not, but openness follows from `IsStrongBundleIsoOn` (its base map is an
    sc-diffeomorphism on `U`, `IsScSmoothOn.isOpen`) and finiteness from `IsProperCovering`;
  - (3): B quantifies over the smoothness proofs and paracompactness instances, the project fixes
    them; all are propositions, so the strong bundle isomorphisms are the same (proof
    irrelevance); B's `liftB F` is the project's `fibredLift P F` (definitionally).
* `B ⇒ A`: B is a statement about the definitions and implies none of A's theorems; they are
  re-proved outright (`isScSmoothMap_fibredSnd` by the project's two-line argument, the `rfl`
  lemmas by `rfl`, the identity example by the project's construction, re-done with our own
  smoothness proof of `pr₂` in place of the banned one; the trivial-bundle example is the identity
  example).  **B is not used.**

**Harness note.**  The banned `isScSmoothMap_fibredSnd` occurs in the *statement* of the project's
definition: the field `isStrongBundleIso_fibredLift` of `IsProperStrongBundleCovering` has type
`… (BW.pullback F.isScSmoothMap_fibredSnd) …`.  So every proof that constructs or destructs an
`IsProperStrongBundleCovering` reaches it through the type of `IsProperStrongBundleCovering.mk` or
of the projection, and plain `#rt_check` fails on both directions for that name only (recorded with
`#guard_msgs`; `#rt_check_soft` does not help, the use is not in a `_proof_N`).  As in V7_40/V8_25,
`#rt_check_except_defs` below is the harness traversal `rtCollect` with the constructor,
recursor and projections of `IsProperStrongBundleCovering` not unfolded; it passes on both
directions.
-/

namespace RoundTrip.V8_37
open Polyfold Set Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpFunctor.isScSmoothMap_fibredSnd.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.pullbackProj_fibredBundleEquiv.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.fibredBundleEquiv_symm_fibredLift.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.isProperStrongBundleCovering_id.{0}) ∧
  (type_of% @Polyfold.TrivialBundle.epBundle_isProperStrongBundleCovering)

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.isScSmoothMap_fibredSnd.{0},
    @Polyfold.EpStrongBundle.pullbackProj_fibredBundleEquiv.{0},
    @Polyfold.EpStrongBundle.fibredBundleEquiv_symm_fibredLift.{0},
    @Polyfold.EpStrongBundle.isProperStrongBundleCovering_id.{0},
    @Polyfold.TrivialBundle.epBundle_isProperStrongBundleCovering⟩

/-! ### `A ⇒ B`: the two definitions agree -/

theorem A_to_B : A → B := by
  intro hA ObjY MorY ObjX MorX _ _ _ _ _ _ _ _ _ _ _ _ Y X W _ _ _ P _ _ BW _ V _ _ _ Q _ _ BV _
    EW EV F A
  obtain ⟨hsnd, -⟩ := hA
  constructor
  · rintro ⟨hA', -, hsurj, hF, hloc, hev, hsY, _, hS, _, hpr, _, g, Ψ, hiso⟩
    refine ⟨hA'.liftFunctor, rfl, ?_⟩
    exact
      { isStrongBundleFunctor := hA'.isStrongBundleFunctor_liftFunctor
        surjective := hsurj
        isProperCovering := hF
        isLocalStrongBundleIso := fun y => by
          obtain ⟨U, U', -, hy, h⟩ := hloc y
          exact ⟨U, U', hy, h⟩
        evenlyCovered := fun x => by
          obtain ⟨-, U, U', hU, hx, hdisj, hU', hcov⟩ := hev x
          exact ⟨U, U', hU, hx, hdisj, fun y hy => ⟨(hU' y hy).2.1, (hU' y hy).2.2⟩, hcov⟩
        -- ascribed with B's own smoothness proofs, so that the term does not mention the
        -- project's `isScSmoothMap_fibredSnd` (the field type does; equal by proof irrelevance)
        isStrongBundleIso_fibredLift := (⟨g, Ψ, hiso⟩ : ∃ g Ψ, (BW.pullback hsY).IsStrongBundleIso
          (BW.pullback hpr) F.fibredMap (liftB F) g Ψ) }
  · rintro ⟨A', rfl, h⟩
    have hA' := h.isStrongBundleFunctor.isMap
    have := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
    have := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
    have := BW.paracompactSpace_pullback (MPolyfold.subPolyfold
      (MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src F.isScSmoothMap_obj))
      F.fibredSnd
    refine ⟨hA', hA'.isStrongBundleMap.covers, h.surjective, h.isProperCovering, fun y => ?_,
      fun x => ?_, ?_⟩
    · obtain ⟨U, U', hy, hU⟩ := h.isLocalStrongBundleIso y
      exact ⟨U, U', hU.isScDiffeoOn_base.choose_spec.isScSmoothOn.isOpen, hy, hU⟩
    · obtain ⟨U, U', hU, hx, hdisj, hU', hcov⟩ := h.evenlyCovered x
      exact ⟨h.isProperCovering.finite_fiber x, U, U', hU, hx, hdisj, fun y hy =>
        ⟨(hU' y hy).2.isScDiffeoOn_base.choose_spec.isScSmoothOn.isOpen, (hU' y hy).1,
          (hU' y hy).2⟩, hcov⟩
    · have h3 : ∃ g Ψ, (BW.pullback Y.isScSmoothMap_src).IsStrongBundleIso
          (BW.pullback (hsnd F)) F.fibredMap (EpStrongBundle.fibredLift P F) g Ψ :=
        h.isStrongBundleIso_fibredLift
      obtain ⟨g, Ψ, hiso⟩ := h3
      exact ⟨Y.isScSmoothMap_src, inferInstance,
        MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src F.isScSmoothMap_obj,
        inferInstance, hsnd F, inferInstance, g, Ψ, hiso⟩

/-! ### `B ⇒ A`: `A` re-proved outright (B is not used) -/

section
variable {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY] {Y : EpGroupoid ObjY MorY}
  {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX] {X : EpGroupoid ObjX MorX}

/-- `pr₂ : 𝐗 ₛ×_F Y → Y` is sc-smooth (the project's argument). -/
theorem fibredSnd_smooth (F : EpFunctor Y X) [ParacompactSpace (MorX × ObjY)]
    [ParacompactSpace (MPolyfold.fibredProduct X.src F.obj)] :
    (MPolyfold.subPolyfold (MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src
      F.isScSmoothMap_obj)).IsScSmoothMap Y.PObj F.fibredSnd :=
  (MPolyfold.isScSmoothMap_snd X.PMor Y.PObj).comp
    (MPolyfold.subPolyfold_inclusion_isScSmooth _)

end

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]

open EpStrongBundle in
variable (B) in
/-- Definition 8.10 (3) for the identity (the project's construction, with `fibredSnd_smooth`). -/
theorem fibredLift_id [ParacompactSpace (Mor × Obj)]
    [ParacompactSpace (MPolyfold.fibredProduct X.src (EpFunctor.id X).obj)]
    [ParacompactSpace (pullbackSpace P (EpFunctor.id X).fibredSnd)] :
    (B.pullback X.isScSmoothMap_src).IsStrongBundleIso
      (B.pullback (fibredSnd_smooth (EpFunctor.id X))) (EpFunctor.id X).fibredMap
      (fibredLift P (EpFunctor.id X)) (fun p => (p : Mor × Obj).1)
      (pullbackMap P (EpFunctor.id X).fibredSnd P X.src (StrongBundle.IsStrongBundleMap.id B).covers
        (g := fun p => (p : Mor × Obj).1) fun p => p.2) where
  toMap := StrongBundle.isStrongBundleMap_pullbackMap X.isScSmoothMap_src
    (fibredSnd_smooth (EpFunctor.id X)) (StrongBundle.IsStrongBundleMap.id B)
    EpFunctor.isScDiffeoOn_fibredMap_id.isScSmoothOn fun _ => rfl
  invMap := StrongBundle.isStrongBundleMap_pullbackMap (fibredSnd_smooth (EpFunctor.id X))
    X.isScSmoothMap_src (StrongBundle.IsStrongBundleMap.id B)
    EpFunctor.isScDiffeoOn_fibredMap_id.isScSmoothOn_inv fun p => p.2
  left_inv _ := rfl
  right_inv r := by
    have hr : X.src ((r : MPolyfold.fibredProduct X.src (EpFunctor.id X).obj × W).1 :
        Mor × Obj).1 = ((r : MPolyfold.fibredProduct X.src (EpFunctor.id X).obj × W).1 :
        Mor × Obj).2 := (r : MPolyfold.fibredProduct X.src (EpFunctor.id X).obj × W).1.2
    exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext rfl hr)) rfl)

/-- Definition 8.10 for the identity (the project's construction). -/
theorem psbCovering_id (E : EpStrongBundle X B) :
    E.IsProperStrongBundleCovering E (EpFunctor.id X) (EpFunctor.id E.toEpGroupoid) where
  isStrongBundleFunctor := E.isStrongBundleFunctor_id
  surjective := surjective_id
  isProperCovering := EpFunctor.isProperCovering_id
  isLocalStrongBundleIso y :=
    ⟨univ, univ, mem_univ y, StrongBundle.isStrongBundleIsoOn_id isOpen_univ⟩
  evenlyCovered x := by
    refine ⟨univ, fun _ => univ, isOpen_univ, mem_univ x, ?_,
      fun _ _ => ⟨mem_univ _, StrongBundle.isStrongBundleIsoOn_id isOpen_univ⟩, ?_⟩
    · rw [EpFunctor.preimage_obj_id]
      exact pairwiseDisjoint_singleton _ _
    · rw [EpFunctor.preimage_obj_id, biUnion_singleton, preimage_univ]
  isStrongBundleIso_fibredLift := by
    have := MPolyfold.paracompactSpace_prod X.PMor X.PObj
    have := (X.PMor.prod X.PObj).paracompactSpace_subtype
      (MPolyfold.fibredProduct X.src (EpFunctor.id X).obj)
    have := B.paracompactSpace_pullback (MPolyfold.subPolyfold
      (MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src
        (EpFunctor.id X).isScSmoothMap_obj)) (EpFunctor.id X).fibredSnd
    exact (⟨_, _, fibredLift_id B⟩ : ∃ g Ψ, (B.pullback X.isScSmoothMap_src).IsStrongBundleIso
      (B.pullback (fibredSnd_smooth (EpFunctor.id X))) (EpFunctor.id X).fibredMap
      (EpStrongBundle.fibredLift P (EpFunctor.id X)) g Ψ)

end

theorem B_to_A : B → A := by
  intro _
  refine ⟨fun F _ _ => fibredSnd_smooth F, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩,
    fun E => psbCovering_id E, fun n k => psbCovering_id (TrivialBundle.epBundle n k)⟩

/-! ### The checks -/

open Lean Elab Command in
/-- `#rt_check_except_defs T [nᵢ]`: the proof of `T` reaches the banned `nᵢ` only through the
constructor, recursor and projections of the structure `IsProperStrongBundleCovering` (whose
field type mentions `isScSmoothMap_fibredSnd`). -/
elab "#rt_check_except_defs " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let S := `Polyfold.EpStrongBundle.IsProperStrongBundleCovering
  let stop : NameSet := [S ++ `mk, S ++ `rec, S ++ `casesOn, S ++ `isStrongBundleFunctor,
    S ++ `surjective, S ++ `isProperCovering, S ++ `isLocalStrongBundleIso, S ++ `evenlyCovered,
    S ++ `isStrongBundleIso_fibredLift].foldl (·.insert ·) {}
  let used := rtCollect env roots.toList stop
  if used.contains ``sorryAx then throwError "FAIL: {t.getId} contains sorry"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  unless bad.isEmpty do
    throwError "FAIL: {t.getId} uses {bad} outside the structure IsProperStrongBundleCovering"
  logInfo m!"OK: {t.getId} reaches the banned theorems only through the constructor/projections of IsProperStrongBundleCovering"

/--
error: rt_check FAIL: RoundTrip.V8_37.A_to_B uses [Polyfold.EpFunctor.isScSmoothMap_fibredSnd]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V8_37.A_to_B [Polyfold.EpFunctor.isScSmoothMap_fibredSnd,
  Polyfold.EpStrongBundle.pullbackProj_fibredBundleEquiv,
  Polyfold.EpStrongBundle.fibredBundleEquiv_symm_fibredLift,
  Polyfold.EpStrongBundle.isProperStrongBundleCovering_id,
  Polyfold.TrivialBundle.epBundle_isProperStrongBundleCovering]
/--
error: rt_check FAIL: RoundTrip.V8_37.B_to_A uses [Polyfold.EpFunctor.isScSmoothMap_fibredSnd]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V8_37.B_to_A [Polyfold.EpFunctor.isScSmoothMap_fibredSnd,
  Polyfold.EpStrongBundle.pullbackProj_fibredBundleEquiv,
  Polyfold.EpStrongBundle.fibredBundleEquiv_symm_fibredLift,
  Polyfold.EpStrongBundle.isProperStrongBundleCovering_id,
  Polyfold.TrivialBundle.epBundle_isProperStrongBundleCovering]
#rt_check_except_defs RoundTrip.V8_37.A_to_B [Polyfold.EpFunctor.isScSmoothMap_fibredSnd,
  Polyfold.EpStrongBundle.pullbackProj_fibredBundleEquiv,
  Polyfold.EpStrongBundle.fibredBundleEquiv_symm_fibredLift,
  Polyfold.EpStrongBundle.isProperStrongBundleCovering_id,
  Polyfold.TrivialBundle.epBundle_isProperStrongBundleCovering]
#rt_check_except_defs RoundTrip.V8_37.B_to_A [Polyfold.EpFunctor.isScSmoothMap_fibredSnd,
  Polyfold.EpStrongBundle.pullbackProj_fibredBundleEquiv,
  Polyfold.EpStrongBundle.fibredBundleEquiv_symm_fibredLift,
  Polyfold.EpStrongBundle.isProperStrongBundleCovering_id,
  Polyfold.TrivialBundle.epBundle_isProperStrongBundleCovering]
#rt_overlap RoundTrip.V8_37.B_to_A [Polyfold.EpFunctor.isScSmoothMap_fibredSnd,
  Polyfold.EpStrongBundle.pullbackProj_fibredBundleEquiv,
  Polyfold.EpStrongBundle.fibredBundleEquiv_symm_fibredLift,
  Polyfold.EpStrongBundle.isProperStrongBundleCovering_id,
  Polyfold.TrivialBundle.epBundle_isProperStrongBundleCovering]

end RoundTrip.V8_37
