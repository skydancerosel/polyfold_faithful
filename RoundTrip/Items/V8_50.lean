import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_50

/-!
Round trip for V8_50 (2021 Definition 8.5.9, proper strong bundle covering functors, with the
new condition (0)).

The item lists the definition `EpStrongBundle.IsProperStrongBundleCovering2021` (vocabulary) and
four theorems: `IsProperStrongBundleCovering.isProperStrongBundleCovering2021` (the 2017 notion
for a functor gives the 2021 notion for its object map), `isProperStrongBundleCovering2021_iff`
(the 2021 notion for `A` iff `A` is the object map of a unique functor satisfying the 2017
notion), and the witnesses `isProperStrongBundleCovering2021_id`,
`TrivialBundle.epBundle_isProperStrongBundleCovering2021`.  `A` is the conjunction of their
types, universes at `0` (the last has none).

`B` says `IsProperStrongBundleCovering2021 EW EV F A` iff `A` is a strong bundle map with
`Q ∘ A = F ∘ P`, (0) holds, and some functor `Â` with `Â.obj = A`,
`Â(ψ, w) = (F(ψ), A(w))` satisfies the project's 2017 `IsProperStrongBundleCovering`.

* `A ⇒ B`: `→` from `isProperStrongBundleCovering2021_iff` (the functor it gives), with
  `IsProperStrongBundleCovering.mor_val` for the morphism formula and the fields `isMap` of the
  structure for the strong bundle map, the square and (0); `←` from
  `isProperStrongBundleCovering2021` applied to `Â`.
* `B ⇒ A`: the 2017 ⇒ 2021 implication is B's `←` (with `IsStrongBundleFunctor.μ_comm` for (0)
  and `mor_val`); the `iff` is B's `→` plus uniqueness (two functors with the same object map and
  `mor_val` are equal, `EpFunctor.ext`); the witnesses are B's `←` for the identity functor
  (the project's 2017 witness `isProperStrongBundleCovering_id`).
-/

namespace RoundTrip.V8_50
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpStrongBundle.IsProperStrongBundleCovering.isProperStrongBundleCovering2021.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.isProperStrongBundleCovering2021_iff.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.isProperStrongBundleCovering2021_id.{0}) ∧
  (type_of% @Polyfold.TrivialBundle.epBundle_isProperStrongBundleCovering2021)

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.IsProperStrongBundleCovering.isProperStrongBundleCovering2021.{0},
    @Polyfold.EpStrongBundle.isProperStrongBundleCovering2021_iff.{0},
    @Polyfold.EpStrongBundle.isProperStrongBundleCovering2021_id.{0},
    @Polyfold.TrivialBundle.epBundle_isProperStrongBundleCovering2021⟩

theorem A_to_B : A → B := by
  intro hA ObjY MorY _ _ _ _ _ _ Y ObjX MorX _ _ _ _ _ _ X W _ _ _ P _ _ BW _ V _ _ _ Q _ _ BV _
    EW EV F Am
  constructor
  · intro h
    obtain ⟨Ψ, ⟨hΨA, hΨ⟩, -⟩ := hA.2.1.1 h
    refine ⟨h.isMap.isStrongBundleMap, h.isMap.isStrongBundleMap.covers,
      fun ψ w hw _ => (h.isMap.map_μ ψ w hw).symm, Ψ, hΨA, fun m => ?_, hΨ⟩
    rw [hΨ.mor_val m, hΨA]
  · rintro ⟨-, -, -, Ψ, hΨA, -, hΨ⟩
    have h := hA.1 hΨ
    rw [hΨA] at h
    exact h

section
variable {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY] {Y : EpGroupoid ObjY MorY}
  {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX] {X : EpGroupoid ObjX MorX}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → ObjY}
  [∀ y, AddCommGroup (P ⁻¹' {y})] [∀ y, Module ℝ (P ⁻¹' {y})] {BW : StrongBundle Y.PObj P}
  [ParacompactSpace (pullbackSpace P Y.src)]
  {V : Type} [TopologicalSpace V] [T2Space V] [ParacompactSpace V] {Q : V → ObjX}
  [∀ x, AddCommGroup (Q ⁻¹' {x})] [∀ x, Module ℝ (Q ⁻¹' {x})] {BV : StrongBundle X.PObj Q}
  [ParacompactSpace (pullbackSpace Q X.src)]
  {EW : EpStrongBundle Y BW} {EV : EpStrongBundle X BV} {F : EpFunctor Y X}

/-- From `B`: the 2017 notion for `Ψ` gives the 2021 notion for `Ψ.obj`. -/
theorem of2017 (hB : B) {Ψ : EpFunctor EW.toEpGroupoid EV.toEpGroupoid}
    (h : EW.IsProperStrongBundleCovering EV F Ψ) :
    EW.IsProperStrongBundleCovering2021 EV F Ψ.obj :=
  (hB ObjY MorY Y ObjX MorX X W P BW V Q BV EW EV F Ψ.obj).2
    ⟨h.isStrongBundleFunctor.isStrongBundleMap_obj,
      h.isStrongBundleFunctor.isStrongBundleMap_obj.covers,
      fun ψ w hw hv => h.isStrongBundleFunctor.μ_comm ψ w hw hv, Ψ, rfl, fun m => h.mor_val m, h⟩

/-- From `B`: the `iff` of the project. -/
theorem iff2021 (hB : B) {Am : W → V} :
    EW.IsProperStrongBundleCovering2021 EV F Am ↔
      ∃! Ψ : EpFunctor EW.toEpGroupoid EV.toEpGroupoid,
        Ψ.obj = Am ∧ EW.IsProperStrongBundleCovering EV F Ψ := by
  constructor
  · intro h
    obtain ⟨-, -, -, Ψ, hΨA, -, hΨ⟩ := (hB ObjY MorY Y ObjX MorX X W P BW V Q BV EW EV F Am).1 h
    refine ⟨Ψ, ⟨hΨA, hΨ⟩, fun Ψ' hΨ' => EpFunctor.ext (hΨ'.1.trans hΨA.symm)
      (funext fun m => Subtype.ext ?_)⟩
    rw [hΨ'.2.mor_val m, hΨ.mor_val m, hΨ'.1, hΨA]
  · rintro ⟨Ψ, ⟨rfl, h⟩, -⟩
    exact of2017 hB h

end

/-- From `B`: the identity is a proper strong bundle covering functor in the 2021 sense. -/
theorem id2021 (hB : B) {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    {X : EpGroupoid Obj Mor} {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W]
    {P : W → Obj} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    {SB : StrongBundle X.PObj P} [ParacompactSpace (pullbackSpace P X.src)]
    (E : EpStrongBundle X SB) : E.IsProperStrongBundleCovering2021 E (EpFunctor.id X) id :=
  of2017 hB (E.isProperStrongBundleCovering_id)

theorem B_to_A : B → A := fun hB =>
  ⟨fun h => of2017 hB h, iff2021 hB, fun E => id2021 hB E,
    fun n k => id2021 hB (TrivialBundle.epBundle n k)⟩

#rt_check RoundTrip.V8_50.A_to_B
  [Polyfold.EpStrongBundle.IsProperStrongBundleCovering.isProperStrongBundleCovering2021,
  Polyfold.EpStrongBundle.isProperStrongBundleCovering2021_iff,
  Polyfold.EpStrongBundle.isProperStrongBundleCovering2021_id,
  Polyfold.TrivialBundle.epBundle_isProperStrongBundleCovering2021]
#rt_check RoundTrip.V8_50.B_to_A
  [Polyfold.EpStrongBundle.IsProperStrongBundleCovering.isProperStrongBundleCovering2021,
  Polyfold.EpStrongBundle.isProperStrongBundleCovering2021_iff,
  Polyfold.EpStrongBundle.isProperStrongBundleCovering2021_id,
  Polyfold.TrivialBundle.epBundle_isProperStrongBundleCovering2021]
#rt_overlap RoundTrip.V8_50.B_to_A
  [Polyfold.EpStrongBundle.IsProperStrongBundleCovering.isProperStrongBundleCovering2021,
  Polyfold.EpStrongBundle.isProperStrongBundleCovering2021_iff,
  Polyfold.EpStrongBundle.isProperStrongBundleCovering2021_id,
  Polyfold.TrivialBundle.epBundle_isProperStrongBundleCovering2021]

end RoundTrip.V8_50
