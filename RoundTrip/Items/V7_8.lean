import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_8

/-! Round trip for V7_8 (Definition 7.6, p. 228: tame ep-groupoids; then `𝐗` is tame).

`A` is the conjunction of the types of the three listed theorems, universes instantiated at `0`
(`B` lives in `Type`): `MPolyfold.IsScDiffeoOn.exists_tame_chart` (a tame chart transported along
an sc-diffeomorphism `U → V`), `MPolyfold.IsLocalScDiffeo.isTame` (tameness pulls back along a
local sc-diffeomorphism) and `MPolyfold.IsLocalScDiffeo.isTame_iff_of_surjective`.  The listed
definitions `EpGroupoid.IsTame` and `MPolyfold.IsTame` are vocabulary; `B` (a) checks the first
against the text (`EpGroupoid.IsTame X ↔ X.PObj.IsTame`, `Iff.rfl`).

* `A → B`: (a) is `Iff.rfl`; (b) is `isTame` applied to `s : 𝐗 → X`
  (`X.isLocalScDiffeo_src`); (c) is `isTame`.
* `B → A`: `isTame` is (c); the backward half of `isTame_iff_of_surjective` is (c).
  `exists_tame_chart` (a statement about a single sc-diffeomorphism between open subsets, with no
  global local sc-diffeomorphism around) and the forward half of `isTame_iff_of_surjective`
  (tameness pushed forward along a surjective local sc-diffeomorphism) are not consequences of
  `B`; they are re-proved outright here from the project's chart transport
  (`transportChart`, `IsTame.exists_chart`, `isTame_of_forall_exists_chart`). -/

namespace RoundTrip.V7_8
open Polyfold MPolyfold Set Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.IsScDiffeoOn.exists_tame_chart.{0, 0}) ∧
  (type_of% @Polyfold.MPolyfold.IsLocalScDiffeo.isTame.{0, 0}) ∧
  (type_of% @Polyfold.MPolyfold.IsLocalScDiffeo.isTame_iff_of_surjective.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.IsScDiffeoOn.exists_tame_chart.{0, 0},
    @Polyfold.MPolyfold.IsLocalScDiffeo.isTame.{0, 0},
    @Polyfold.MPolyfold.IsLocalScDiffeo.isTame_iff_of_surjective.{0, 0}⟩

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  intro hA
  refine ⟨fun Obj Mor _ _ _ _ _ _ X => ⟨Iff.rfl, fun h => ?_⟩, ?_⟩
  · exact hA.2.1 X.isLocalScDiffeo_src h
  · intro Y Z _ _ _ _ _ _ P Q f hf hQ
    exact hA.2.1 hf hQ

/-! ### `B → A` -/

/-- `exists_tame_chart`, re-proved outright (the chart transport of the project). -/
theorem exists_tame_chart' {X Y : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {P : MPolyfold X} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
    {f : X → Y} {g : Y → X} {U : Set X} {V : Set Y}
    (h : P.IsScDiffeoOn Q f g U V) (hQ : Q.IsTame) {x : X} (hx : x ∈ U) :
    ∃ φ : MChart X, P.IsChart φ ∧ x ∈ φ.source ∧ IsTameRetract φ.model.E φ.model.C φ.model.O := by
  obtain ⟨ψ, hψ, hy, Rψ, hRψ, hRt⟩ := IsTame.exists_chart Q hQ (f x)
  obtain ⟨W', hW', heq⟩ := ψ.exists_isOpen_image_eq (s := V ∩ ψ.source) inter_subset_right
    (h.isOpen_target.inter ψ.isOpen_source)
  refine ⟨transportChart h ψ, transportChart_isChart h hψ, ⟨hx, hy⟩, Rψ.restrict hW', ?_,
    fun n W T hT => (hRt n W T hT).restrict hW'⟩
  have h1 : (Rψ.restrict hW').retract = ψ '' (V ∩ ψ.source) := by
    rw [Rψ.restrict_retract, hRψ]; exact heq.symm
  exact h1

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun h hQ _ hx => exists_tame_chart' h hQ hx, ?_, ?_⟩
  · intro X _ _ _ P Y _ _ _ Q f hf hQ
    exact hB.2 X Y P Q f hf hQ
  · intro X _ _ _ P Y _ _ _ Q f hf hsurj
    refine ⟨fun hP => isTame_of_forall_exists_chart _ fun y => ?_, hB.2 X Y P Q f hf⟩
    obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨U, V, g, hx, hd⟩ := hf x
    exact exists_tame_chart' hd.symm hP (hd.mapsTo hx)

#rt_check RoundTrip.V7_8.A_to_B [Polyfold.MPolyfold.IsScDiffeoOn.exists_tame_chart,
  Polyfold.MPolyfold.IsLocalScDiffeo.isTame,
  Polyfold.MPolyfold.IsLocalScDiffeo.isTame_iff_of_surjective]
#rt_check RoundTrip.V7_8.B_to_A [Polyfold.MPolyfold.IsScDiffeoOn.exists_tame_chart,
  Polyfold.MPolyfold.IsLocalScDiffeo.isTame,
  Polyfold.MPolyfold.IsLocalScDiffeo.isTame_iff_of_surjective]
#rt_overlap RoundTrip.V7_8.B_to_A [Polyfold.MPolyfold.IsScDiffeoOn.exists_tame_chart,
  Polyfold.MPolyfold.IsLocalScDiffeo.isTame,
  Polyfold.MPolyfold.IsLocalScDiffeo.isTame_iff_of_surjective]

end RoundTrip.V7_8
