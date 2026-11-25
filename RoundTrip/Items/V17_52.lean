import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_52

set_option maxSynthPendingDepth 3

/-! Round trip for V17_52 (2021 Proposition 17.2.15, p. 781: the natural M-polyfold structure on
`M(TΨ, TΨ')`, the maps (17.42) as charts; `s, t` local sc-diffeomorphisms, `ι` an
sc-diffeomorphism, `u`, `m` sc-smooth).

`A` is the conjunction of the types of `isScDiffeoOn_tangentTrChartExt`,
`tangentTr_isLocalScDiffeo_src`, `tangentTr_isScSmoothMap_mul` and `proposition_17_2_15`, universe
`0` (`B` uses `GCT.{0}`); `tangentTrPolyfold` is vocabulary.

* `A_to_B` (from the main conjunct alone): `N := natStr` (the project's `tangentTrPolyfold` with
  the `T2Space`/`ParacompactSpace` instances of `TTrM`; `TTrM`'s topology `tangentTrTopology` is
  definitionally `B`'s `natTop`).  For the charts: `f := tangentTrChartExt`, `g := s`; the project
  states the sc-diffeomorphism onto `Ts⁻¹`-preimage of the sheet, which is shown to be the range of
  the map (17.42) (`mapsTo`, `right_inv` and `tangentTrChartExt = map (17.42)` on `TU(o)`); its
  openness is the openness carried by `IsScSmoothOn`.  The rest is the conjuncts, with
  `ι`'s sc-smoothness the first half of the project's sc-diffeomorphism.
* `B_to_A` is not proved.  `B` gives SOME M-polyfold structure `N.M` on `(M(TΨ₁, TΨ₂), natTop)` for
  which the maps (17.42) are sc-diffeomorphisms onto open sets; `A` is about the project's specific
  `tangentTrPolyfold` (Part I's `TM(Ψ₁, Ψ₂)` transported).  Getting `A` from `B` needs the
  uniqueness of an M-polyfold structure with a given covering atlas (the identity
  `N.M → tangentTrPolyfold` is, on the range of each map (17.42), `chart ∘ chart⁻¹`, hence
  sc-smooth both ways, by locality of sc-smoothness), and then transporting every property of `A`
  along that identity, including sc-smoothness on the sub-M-polyfold fibred product (for `m`).
  This is true but is substantial M-polyfold glue, not done here.
-/

namespace RoundTrip.V17_52
open Polyfold GCT.PolyfoldConstruction Topology Set

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.isScDiffeoOn_tangentTrChartExt.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.tangentTr_isLocalScDiffeo_src.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.tangentTr_isScSmoothMap_mul.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_15.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.isScDiffeoOn_tangentTrChartExt.{0},
    @Polyfold.GCT.PolyfoldConstruction.tangentTr_isLocalScDiffeo_src.{0},
    @Polyfold.GCT.PolyfoldConstruction.tangentTr_isScSmoothMap_mul.{0},
    @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_15.{0}⟩

/-- The project's structure as a `NatStr`. -/
noncomputable def natStr {C : GCT.{0}} (S : C.PolyfoldConstruction) (hU : S.HasUniformizers) :
    NatStr S hU where
  t2 Ψ₁ Ψ₂ := (inferInstance : T2Space (S.TTrM hU Ψ₁ Ψ₂))
  pc Ψ₁ Ψ₂ := (inferInstance : ParacompactSpace (S.TTrM hU Ψ₁ Ψ₂))
  P Ψ₁ Ψ₂ := S.tangentTrPolyfold hU Ψ₁ Ψ₂

theorem main_to_B :
    (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_15.{0}) → B := by
  intro h C S hU
  refine ⟨natStr S hU, fun Ψ₁ Ψ₂ o T => ?_, fun Ψ₁ Ψ₂ => (h hU Ψ₁ Ψ₂ Ψ₁).2.1,
    fun Ψ₁ Ψ₂ => (h hU Ψ₁ Ψ₂ Ψ₁).2.2.1, fun Ψ₁ Ψ₂ => (h hU Ψ₁ Ψ₂ Ψ₁).2.2.2.1.isScSmoothOn,
    fun Ψ => (h hU Ψ Ψ Ψ).2.2.2.2.1, fun Ψ₁ Ψ₂ Ψ₃ => ⟨(h hU Ψ₁ Ψ₂ Ψ₃).2.2.1.isScSmoothMap,
      (h hU Ψ₁ Ψ₂ Ψ₃).2.2.2.2.2⟩⟩
  obtain ⟨heq, hd⟩ := (h hU Ψ₁ Ψ₂ Ψ₁).1 T
  -- the image of the chart is the target set of the sc-diffeomorphism
  have hW : Set.range (chart (natStr S hU) T) =
      univ ∩ (tangentTrHomeomorph hU Ψ₁ Ψ₂).symm ⁻¹'
        (S.transPolyfold Ψ₁ Ψ₂).tangentPreimage T.carrier := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      have := hd.mapsTo k.2
      rw [heq k] at this
      exact this
    · intro hx
      refine ⟨⟨_, hd.mapsTo_inv hx⟩, ?_⟩
      exact (heq ⟨_, hd.mapsTo_inv hx⟩).symm.trans (hd.right_inv x hx)
  refine ⟨hW ▸ hd.isScSmoothOn_inv.isOpen, tangentTrChartExt hU T,
    fun x : S.TTrM hU Ψ₁ Ψ₂ => x.src, fun k => heq k, ?_⟩
  rw [hW]
  exact hd

theorem A_to_B : A → B := fun h => main_to_B h.2.2.2

/-! ### Harness note

The statements of `tangentTr_isScSmoothMap_mul` and `proposition_17_2_15` contain the banned
`tangentTr_isLocalScDiffeo_src` as a term: `MPolyfold.IsScSmoothOnFibredProduct` takes the proof
that `s` is a local sc-diffeomorphism as an argument (it builds the sub-M-polyfold
`M(TΨ₂, TΨ₃) ₛ×ₜ M(TΨ₁, TΨ₂)` from it).  Every term whose type mentions `A` (or the main
conjunct) therefore reaches it, in the statement, not in the proof; `#rt_check` and
`#rt_check_soft` both report it (recorded below).  No other banned declaration is reached. -/

/--
error: rt_check FAIL: RoundTrip.V17_52.A_to_B uses [Polyfold.GCT.PolyfoldConstruction.tangentTr_isLocalScDiffeo_src]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V17_52.A_to_B [Polyfold.GCT.PolyfoldConstruction.isScDiffeoOn_tangentTrChartExt,
  Polyfold.GCT.PolyfoldConstruction.tangentTr_isLocalScDiffeo_src,
  Polyfold.GCT.PolyfoldConstruction.tangentTr_isScSmoothMap_mul,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_15]
/--
error: rt_check_soft FAIL: RoundTrip.V17_52.A_to_B uses [Polyfold.GCT.PolyfoldConstruction.tangentTr_isLocalScDiffeo_src]
-/
#guard_msgs (whitespace := lax) in
#rt_check_soft RoundTrip.V17_52.A_to_B [Polyfold.GCT.PolyfoldConstruction.isScDiffeoOn_tangentTrChartExt,
  Polyfold.GCT.PolyfoldConstruction.tangentTr_isLocalScDiffeo_src,
  Polyfold.GCT.PolyfoldConstruction.tangentTr_isScSmoothMap_mul,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_15]
/--
error: rt_check FAIL: RoundTrip.V17_52.main_to_B uses [Polyfold.GCT.PolyfoldConstruction.tangentTr_isLocalScDiffeo_src]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V17_52.main_to_B [Polyfold.GCT.PolyfoldConstruction.isScDiffeoOn_tangentTrChartExt,
  Polyfold.GCT.PolyfoldConstruction.tangentTr_isLocalScDiffeo_src,
  Polyfold.GCT.PolyfoldConstruction.tangentTr_isScSmoothMap_mul,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_15]
#rt_overlap RoundTrip.V17_52.A_to_B [Polyfold.GCT.PolyfoldConstruction.isScDiffeoOn_tangentTrChartExt,
  Polyfold.GCT.PolyfoldConstruction.tangentTr_isLocalScDiffeo_src,
  Polyfold.GCT.PolyfoldConstruction.tangentTr_isScSmoothMap_mul,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_15]

end RoundTrip.V17_52
