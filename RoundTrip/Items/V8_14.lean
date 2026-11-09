import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_14

/-! Round trip for V8_14 (Theorem 8.1.12 (2017: 8.3): the functor `T : 𝓔𝓟 → 𝓔𝓟`).

`A` is the conjunction of the types of `theorem_8_1_12` and `theorem_8_1_12_tame`, universe
instantiated at `0`; `EP.tangent` and `tangentFunctor` are definitions (vocabulary).  At `u = 0`
both theorems are about `EP.{max 0 1} = EP.{1}`: bundled ep-groupoids whose object and morphism
spaces live in `Type 1`.  `theorem_8_1_12` says `tangentFunctor : EP.{1} ⥤ EP.{1}` sends `A` to
`A.X.tangentEpGroupoid` and `Φ` to `EpFunctor.tangent Φ` (both `rfl`) and satisfies the functor
laws; `theorem_8_1_12_tame` says it preserves tameness.

`B` is stated for ep-groupoids in `Type` (universe `0`), their tangents in `Type 1`, component by
component: (a) `TX` with (8.3)–(8.9) is an ep-groupoid, (b) `(TΦ, T𝚽)` is an sc-smooth functor,
(c) `T(id) = id`, `T(Ψ ∘ Φ) = TΨ ∘ TΦ`, (d) tameness.

**Universe mismatch.**  `EP.{max u 1}` never contains an ep-groupoid in `Type 0`, so `A` cannot
be specialized to `B`'s objects, and `B` cannot be applied to `A`'s objects (in `Type 1`).  Both
directions are therefore proved outright, from non-item project lemmas, without using the
hypothesis (vacuous for the audit):
* `A_to_B`: (a) from the fields of `tangentEpGroupoid` (Theorem 8.1; properness from
  `IsProperMap`), (b) from `EpFunctor.theorem_8_1_11`, (c) from Part I's `tangentMap_id`,
  `tangentMap_comp`, (d) from `MPolyfold.IsTame.tangent`.
* `B_to_A`: `rfl`, `rfl`, the `map_id`/`map_comp` fields of `tangentFunctor`, and
  `EpGroupoid.lemma_8_1_9`. -/

namespace RoundTrip.V8_14
open Polyfold CategoryTheory

/-- The project's statement (universe at `0`, i.e. about `EP.{1}`). -/
def A : Prop :=
  (type_of% @Polyfold.theorem_8_1_12.{0}) ∧ (type_of% @Polyfold.theorem_8_1_12_tame.{0})

theorem A_holds : A := ⟨@Polyfold.theorem_8_1_12.{0}, @Polyfold.theorem_8_1_12_tame.{0}⟩

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

theorem isTUnitB_tUnit (X : EpGroupoid Obj Mor) (q : X.PObj.TangentSpace) :
    IsTUnitB X X.isScSmoothMap_src q (X.tUnit q) :=
  ⟨X.tBase_tUnit q, X.tSrc_tUnit q⟩

theorem eq_tUnit_of_isTUnitB (X : EpGroupoid Obj Mor) {q : X.PObj.TangentSpace}
    {v : X.PMor.TangentSpace} (hv : IsTUnitB X X.isScSmoothMap_src q v) : X.tUnit q = v :=
  X.tangent_ext ((X.tBase_tUnit q).trans hv.1.symm) ((X.tSrc_tUnit q).trans hv.2.symm)

/-- (a): the project's tangent ep-groupoid witnesses `TangentIsEpB`. -/
theorem tangentIsEpB (X : EpGroupoid Obj Mor) : TangentIsEpB X := by
  refine ⟨X.isScSmoothMap_src, X.isScSmoothMap_tgt, X.isScSmoothMap_inv,
    X.tangentEpGroupoid.toGroupoidStr, rfl, rfl, fun k h _ => rfl, fun a => isTUnitB_tUnit X a,
    rfl, X.tangentEpGroupoid.isLocalScDiffeo_src, X.tangentEpGroupoid.isLocalScDiffeo_tgt,
    X.tangentEpGroupoid.isScSmoothMap_unit, X.tangentEpGroupoid.isScSmoothMap_inv,
    fun x => ?_, ?_⟩
  · obtain ⟨V, hV, hx, hp⟩ := X.tangentEpGroupoid.exists_isProperMap x
    exact ⟨V, hV, hx, hp.continuous, fun K hK => hp.isCompact_preimage hK⟩
  · let _ := MPolyfold.paracompactSpace_prod X.PMor.tangentPolyfold X.PMor.tangentPolyfold
    let _ := (X.PMor.tangentPolyfold.prod X.PMor.tangentPolyfold).paracompactSpace_subtype
      (MPolyfold.fibredProduct X.tangentEpGroupoid.src X.tangentEpGroupoid.tgt)
    exact ⟨inferInstance, MPolyfold.isSubMPolyfold_fibredProduct
      X.tangentEpGroupoid.isLocalScDiffeo_src X.tangentEpGroupoid.isLocalScDiffeo_tgt.isScSmoothMap,
      inferInstance, X.tangentEpGroupoid.isScSmoothComp⟩

end

/-- (b): the tangent of an sc-smooth functor witnesses `TangentIsMorB` (Theorem 8.2). -/
theorem tangentIsMorB {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj'] [TopologicalSpace Mor']
    [T2Space Mor'] [ParacompactSpace Mor'] {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}
    (F : EpFunctor X Y) : TangentIsMorB F := by
  obtain ⟨-, -, hso, hsm, hs, ht, hc, hu⟩ := EpFunctor.theorem_8_1_11 F
  refine ⟨X.isScSmoothMap_src, X.isScSmoothMap_tgt, Y.isScSmoothMap_src, Y.isScSmoothMap_tgt,
    hso, hsm, hs, ht, hc, fun a v hv => ?_⟩
  have hv' : X.tUnit a = v := eq_tUnit_of_isTUnitB X hv
  subst hv'
  have h1 : MPolyfold.tangentMap F.isScSmoothMap_mor (X.tUnit a) =
      Y.tUnit (MPolyfold.tangentMap F.isScSmoothMap_obj a) := hu a
  rw [h1]
  exact ⟨isTUnitB_tUnit Y _, fun w hw => eq_tUnit_of_isTUnitB Y hw⟩

/-- `A → B`, proved outright (`A` is about `EP.{1}`, `B` about ep-groupoids in `Type`). -/
theorem A_to_B : A → B := fun _ =>
  ⟨fun _ _ _ _ _ _ _ _ X => tangentIsEpB X,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F => tangentIsMorB F,
    fun _ _ _ _ _ _ _ _ _ => ⟨MPolyfold.isScSmoothMap_id, MPolyfold.isScSmoothMap_id,
      MPolyfold.tangentMap_id, MPolyfold.tangentMap_id⟩,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F G =>
      ⟨G.isScSmoothMap_obj.comp F.isScSmoothMap_obj, G.isScSmoothMap_mor.comp F.isScSmoothMap_mor,
        MPolyfold.tangentMap_comp _ _, MPolyfold.tangentMap_comp _ _⟩,
    fun _ _ _ _ _ _ _ _ _ hX => MPolyfold.IsTame.tangent hX⟩

/-- `B → A`, proved outright (`B` says nothing about ep-groupoids in `Type 1`). -/
theorem B_to_A : B → A := fun _ =>
  ⟨⟨fun _ => rfl, fun _ => rfl, fun A => tangentFunctor.map_id A,
      fun Φ Ψ => tangentFunctor.map_comp Φ Ψ⟩,
    fun A hA => A.X.lemma_8_1_9 hA⟩

#rt_check RoundTrip.V8_14.A_to_B [Polyfold.theorem_8_1_12, Polyfold.theorem_8_1_12_tame]
#rt_check RoundTrip.V8_14.B_to_A [Polyfold.theorem_8_1_12, Polyfold.theorem_8_1_12_tame]
#rt_overlap RoundTrip.V8_14.B_to_A [Polyfold.theorem_8_1_12, Polyfold.theorem_8_1_12_tame]

end RoundTrip.V8_14
