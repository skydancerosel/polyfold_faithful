import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_43

/-! Round trip for V8_43 (2017 §8.5.2 = 2021 §8.6.2, pp. 288–289: the structure of strong bundle
coverings).

`A` is the conjunction of the types of the three listed theorems, universes at `0` (`B` lives in
`Type`): `IsProperStrongBundleCovering.mor_val` (`A(φ, w) = (F(φ), A(w))`),
`IsStrongBundleFunctor.μ_comm` (`μ_X(F φ, A w) = A(μ_Y(φ, w))` for every strong bundle functor)
and `section_8_5_2` (the naturality square on fibres, through `fiberMor` and `fiberEquiv`).  The
listed `IsProperStrongBundleCovering.fiberEquiv` is a definition (vocabulary).

* `A → B`: `B`'s (1) is `A`'s `mor_val`, `B`'s (3) is `A`'s `μ_comm` applied to the strong bundle
  functor part of the covering.  The rest is not in `A` and is proved outright: (0) is `rfl` (the
  structure maps of `(W, 𝐖)`), (2) is the definition `fiberEquiv` (from Definition 8.10 (1)), and
  (4) (`μ_Y`, `μ_X` functors into `Ban`) is the Part I field `StrongBundle.banachable`, the
  project's `fiberMorEquiv`, and the fields `μ_unit`, `μ_comp` of `EpStrongBundle`.
* `B → A`: `mor_val` is `B`'s (1); `section_8_5_2` is `B`'s (3) at `w = v` (both sides unfold to
  `μ_X(F φ, A v)` and `A(μ_Y(φ, v))`).  `μ_comm` is stated for an arbitrary strong bundle functor,
  a wider class than `B`'s proper coverings, so it is re-proved outright from the (non-item)
  lemma `IsStrongBundleFunctor.isMap`. -/

namespace RoundTrip.V8_43
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpStrongBundle.IsProperStrongBundleCovering.mor_val.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.IsStrongBundleFunctor.μ_comm.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.section_8_5_2.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.IsProperStrongBundleCovering.mor_val.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleFunctor.μ_comm.{0},
    @Polyfold.EpStrongBundle.section_8_5_2.{0}⟩

section Outright
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

/-- Every strong bundle over an ep-groupoid gives a functor `μ : X → Ban` (not part of `A`). -/
theorem isBanFunctor_outright (E : EpStrongBundle X B) : IsBanFunctor E :=
  ⟨B.banachable, fun φ => ⟨E.fiberMorEquiv φ, fun _ _ => rfl⟩, fun w _ => E.μ_unit w,
    fun ψ γ w hs h₁ _ _ => E.μ_comp ψ γ w h₁ hs⟩

end Outright

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA ObjY MorY _ _ _ _ _ _ Y ObjX MorX _ _ _ _ _ _ X W _ _ _ P _ _ BW _ V _ _ _ Q _ _ BV _
    EW EV F Aw h
  refine ⟨⟨fun m => ⟨rfl, rfl⟩, fun m => ⟨rfl, rfl⟩⟩, fun m => hA.1 h m,
    fun y => ⟨h.fiberEquiv y, fun _ => rfl⟩,
    fun φ w hw hv => hA.2.1 h.isStrongBundleFunctor φ w hw hv,
    isBanFunctor_outright EW, isBanFunctor_outright EV⟩

/-! ### `B → A` -/

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  · intro ObjY MorY _ _ _ _ _ _ Y ObjX MorX _ _ _ _ _ _ X W _ _ _ P _ _ BW _ V _ _ _ Q _ _ BV _
      EW EV F Aw h q
    exact (hB ObjY MorY Y ObjX MorX X W P BW V Q BV EW EV F Aw h).2.1 q
  · -- `μ_comm` for an arbitrary strong bundle functor: outside `B`, re-proved outright
    intro ObjY MorY _ _ _ _ _ _ Y ObjX MorX _ _ _ _ _ _ X W _ _ _ P _ _ BW _ V _ _ _ Q _ _ BV _
      EW EV F Aw h φ w hw hw'
    exact (h.isMap.map_μ φ w hw).symm
  · intro ObjY MorY _ _ _ _ _ _ Y ObjX MorX _ _ _ _ _ _ X W _ _ _ P _ _ BW _ V _ _ _ Q _ _ BV _
      EW EV F Aw h φ v
    exact (hB ObjY MorY Y ObjX MorX X W P BW V Q BV EW EV F Aw h).2.2.2.1 φ v v.2 _

#rt_check RoundTrip.V8_43.A_to_B [Polyfold.EpStrongBundle.IsProperStrongBundleCovering.mor_val,
  Polyfold.EpStrongBundle.IsStrongBundleFunctor.μ_comm, Polyfold.EpStrongBundle.section_8_5_2]
#rt_check RoundTrip.V8_43.B_to_A [Polyfold.EpStrongBundle.IsProperStrongBundleCovering.mor_val,
  Polyfold.EpStrongBundle.IsStrongBundleFunctor.μ_comm, Polyfold.EpStrongBundle.section_8_5_2]
#rt_overlap RoundTrip.V8_43.B_to_A [Polyfold.EpStrongBundle.IsProperStrongBundleCovering.mor_val,
  Polyfold.EpStrongBundle.IsStrongBundleFunctor.μ_comm, Polyfold.EpStrongBundle.section_8_5_2]
#rt_overlap RoundTrip.V8_43.A_to_B [Polyfold.EpStrongBundle.IsProperStrongBundleCovering.mor_val,
  Polyfold.EpStrongBundle.IsStrongBundleFunctor.μ_comm, Polyfold.EpStrongBundle.section_8_5_2]

end RoundTrip.V8_43
