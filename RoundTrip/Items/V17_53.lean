import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_53

set_option maxSynthPendingDepth 3

/-! Round trip for V17_53 (2021 Proposition 17.2.16, pp. 782–783: `|TC|` metrizable, `TC` a GCT,
`|P|` continuous).

`A` is the conjunction of the types of `isHomeomorph_tangentModelOrbitEquiv`,
`metrizableSpace_tangentOrbit`, `continuous_orbitMap_tangentCatProj` and `proposition_17_2_16`,
universe `u = 0` (`B` uses `GCT.{0}`).

* `A_to_B`: `T := tangentOrbitTopology hU`; `hc` is not needed (the project derives it from `hU`;
  `levelOneGCT hc` has `top := levelOneTopology hc`, and proofs of `hc` are irrelevant).
* `B_to_A`: `B`'s `T` makes `|TΓ_Ψ|` a homeomorphism for the project's chosen family, so it is the
  coinduced topology, i.e. `tangentOrbitTopology hU` (`eq_tangentOrbitTopology`); then everything
  is `B`.  The full / faithful / essentially surjective conjuncts of `proposition_17_2_16` are not
  topological and not in `B`; they are taken from the non-item lemmas `tangentModelFunctor_full`,
  `_faithful`, `_essSurj`.
-/

namespace RoundTrip.V17_53
open Polyfold GCT.PolyfoldConstruction

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.isHomeomorph_tangentModelOrbitEquiv.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.metrizableSpace_tangentOrbit.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.continuous_orbitMap_tangentCatProj.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_16.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.isHomeomorph_tangentModelOrbitEquiv.{0},
    @Polyfold.GCT.PolyfoldConstruction.metrizableSpace_tangentOrbit.{0},
    @Polyfold.GCT.PolyfoldConstruction.continuous_orbitMap_tangentCatProj.{0},
    @Polyfold.GCT.PolyfoldConstruction.proposition_17_2_16.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨hhom, hmet, hcont, -⟩ C S hU hc
  exact ⟨S.tangentOrbitTopology hU, hmet hU, fun c => hhom hU c, hcont hU⟩

/-- A topology on `|TC|` making `|TΓ_Ψ|` a homeomorphism for one covering family is the
project's `tangentOrbitTopology`. -/
theorem eq_tangentOrbitTopology {C : GCT.{0}} {S : C.PolyfoldConstruction}
    (hU : S.HasUniformizers) (T : TopologicalSpace S.tangentCatGroupoid.OrbitSpace)
    (h : @IsHomeomorph _ _ _ T (S.tangentModelFunctor hU (S.tangentCover hU).Ψ).orbitMap) :
    T = S.tangentOrbitTopology hU :=
  (@IsHomeomorph.isQuotientMap _ _ _ T _ h).eq_coinduced

theorem B_to_A : B → A := by
  intro hB
  have key : ∀ {C : GCT.{0}} {S : C.PolyfoldConstruction} (hU : S.HasUniformizers),
      @TopologicalSpace.MetrizableSpace _ (S.tangentOrbitTopology hU) ∧
      (∀ c : S.CoveringFamily,
        @IsHomeomorph _ _ _ (S.tangentOrbitTopology hU) (S.tangentModelFunctor hU c.Ψ).orbitMap) ∧
      @Continuous _ _ (S.tangentOrbitTopology hU)
        (S.levelOneTopology (S.hasCoveringUniformizers_of_hasUniformizers hU))
        S.tangentCatProj.orbitMap := by
    intro C S hU
    obtain ⟨T, hmet, hhom, hcont⟩ := hB C S hU (S.hasCoveringUniformizers_of_hasUniformizers hU)
    obtain rfl := eq_tangentOrbitTopology hU T (hhom _)
    exact ⟨hmet, hhom, hcont⟩
  refine ⟨fun hU c => (key hU).2.1 c, fun hU => (key hU).1, fun hU => (key hU).2.2,
    fun {C S} hU => ⟨fun c => ⟨S.tangentModelFunctor_full hU c.Ψ,
      S.tangentModelFunctor_faithful hU c.Ψ, S.tangentModelFunctor_essSurj hU c.cover, @IsHomeomorph.bijective _ _ _ (S.tangentOrbitTopology hU) _ ((key hU).2.1 c), (key hU).2.1 c⟩,
      (key hU).1, rfl, (key hU).2.2⟩⟩

/-! ### Harness note: the statement of `A` mentions `tangentGCT`

`proposition_17_2_16` states `(S.tangentGCT hU).toGroupoidStr = S.tangentCatGroupoid`, and the
definition `tangentGCT` fills its `metrizable` field with the banned `metrizableSpace_tangentOrbit`
(not abstracted as a `_proof_` field, so `#rt_check_soft` does not separate it).  Every term whose
type mentions `A` therefore reaches it; both checks fail on both directions (recorded below).  To
show that the proofs themselves avoid the banned theorems we also prove both directions for
`A_core`: `A` with that conjunct (which holds by `rfl`) removed, and check those. -/

/-- `A` without the conjunct `(S.tangentGCT hU).toGroupoidStr = S.tangentCatGroupoid`. -/
def A_core : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.isHomeomorph_tangentModelOrbitEquiv.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.metrizableSpace_tangentOrbit.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.continuous_orbitMap_tangentCatProj.{0}) ∧
  ∀ {C : GCT.{0}} {S : C.PolyfoldConstruction} (hU : S.HasUniformizers),
    (∀ (c : S.CoveringFamily),
      (S.tangentModelFunctor hU c.Ψ).toFunctor.Full ∧
        (S.tangentModelFunctor hU c.Ψ).toFunctor.Faithful ∧
          (S.tangentModelFunctor hU c.Ψ).toFunctor.EssSurj ∧
            Function.Bijective (S.tangentModelFunctor hU c.Ψ).orbitMap ∧
              @IsHomeomorph _ _ _ (S.tangentOrbitTopology hU)
                (S.tangentModelFunctor hU c.Ψ).orbitMap) ∧
    @TopologicalSpace.MetrizableSpace S.tangentCatGroupoid.OrbitSpace (S.tangentOrbitTopology hU) ∧
    @Continuous _ _ (S.tangentOrbitTopology hU)
      (S.levelOneTopology (S.hasCoveringUniformizers_of_hasUniformizers hU))
      S.tangentCatProj.orbitMap

theorem A_core_to_B : A_core → B := by
  rintro ⟨hhom, hmet, hcont, -⟩ C S hU hc
  exact ⟨S.tangentOrbitTopology hU, hmet hU, fun c => hhom hU c, hcont hU⟩

theorem B_to_A_core : B → A_core := by
  intro hB
  have key : ∀ {C : GCT.{0}} {S : C.PolyfoldConstruction} (hU : S.HasUniformizers),
      @TopologicalSpace.MetrizableSpace _ (S.tangentOrbitTopology hU) ∧
      (∀ c : S.CoveringFamily,
        @IsHomeomorph _ _ _ (S.tangentOrbitTopology hU) (S.tangentModelFunctor hU c.Ψ).orbitMap) ∧
      @Continuous _ _ (S.tangentOrbitTopology hU)
        (S.levelOneTopology (S.hasCoveringUniformizers_of_hasUniformizers hU))
        S.tangentCatProj.orbitMap := by
    intro C S hU
    obtain ⟨T, hmet, hhom, hcont⟩ := hB C S hU (S.hasCoveringUniformizers_of_hasUniformizers hU)
    obtain rfl := eq_tangentOrbitTopology hU T (hhom _)
    exact ⟨hmet, hhom, hcont⟩
  refine ⟨fun hU c => (key hU).2.1 c, fun hU => (key hU).1, fun hU => (key hU).2.2,
    fun {C S} hU => ⟨fun c => ⟨S.tangentModelFunctor_full hU c.Ψ,
      S.tangentModelFunctor_faithful hU c.Ψ, S.tangentModelFunctor_essSurj hU c.cover,
      @IsHomeomorph.bijective _ _ _ (S.tangentOrbitTopology hU) _ ((key hU).2.1 c),
      (key hU).2.1 c⟩, (key hU).1, (key hU).2.2⟩⟩


/-- The main conjunct (`proposition_17_2_16`, without its `rfl` conjunct on `tangentGCT`). -/
def Main_core : Prop :=
  ∀ {C : GCT.{0}} {S : C.PolyfoldConstruction} (hU : S.HasUniformizers),
    (∀ (c : S.CoveringFamily),
      (S.tangentModelFunctor hU c.Ψ).toFunctor.Full ∧
        (S.tangentModelFunctor hU c.Ψ).toFunctor.Faithful ∧
          (S.tangentModelFunctor hU c.Ψ).toFunctor.EssSurj ∧
            Function.Bijective (S.tangentModelFunctor hU c.Ψ).orbitMap ∧
              @IsHomeomorph _ _ _ (S.tangentOrbitTopology hU)
                (S.tangentModelFunctor hU c.Ψ).orbitMap) ∧
    @TopologicalSpace.MetrizableSpace S.tangentCatGroupoid.OrbitSpace (S.tangentOrbitTopology hU) ∧
    @Continuous _ _ (S.tangentOrbitTopology hU)
      (S.levelOneTopology (S.hasCoveringUniformizers_of_hasUniformizers hU))
      S.tangentCatProj.orbitMap

theorem main_core_to_B : Main_core → B := fun h _ S hU _ =>
  ⟨S.tangentOrbitTopology hU, (h hU).2.1, fun c => ((h hU).1 c).2.2.2.2, (h hU).2.2⟩

theorem B_to_main_core : B → Main_core := fun hB => (B_to_A_core hB).2.2.2

/-- `A` is `A_core` plus a conjunct that holds by `rfl`. -/
theorem A_iff_A_core : A ↔ A_core :=
  ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, fun hU => ⟨(h₄ hU).1, (h₄ hU).2.1, (h₄ hU).2.2.2⟩⟩,
    fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, fun hU => ⟨(h₄ hU).1, (h₄ hU).2.1, rfl, (h₄ hU).2.2⟩⟩⟩

/--
error: rt_check FAIL: RoundTrip.V17_53.A_to_B uses [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_tangentModelOrbitEquiv,
 Polyfold.GCT.PolyfoldConstruction.metrizableSpace_tangentOrbit]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V17_53.A_to_B [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_tangentModelOrbitEquiv,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_tangentOrbit,
  Polyfold.GCT.PolyfoldConstruction.continuous_orbitMap_tangentCatProj,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_16]
/--
error: rt_check FAIL: RoundTrip.V17_53.B_to_A uses [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_tangentModelOrbitEquiv,
 Polyfold.GCT.PolyfoldConstruction.metrizableSpace_tangentOrbit]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V17_53.B_to_A [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_tangentModelOrbitEquiv,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_tangentOrbit,
  Polyfold.GCT.PolyfoldConstruction.continuous_orbitMap_tangentCatProj,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_16]
/--
error: rt_check_soft FAIL: RoundTrip.V17_53.B_to_A uses [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_tangentModelOrbitEquiv,
 Polyfold.GCT.PolyfoldConstruction.metrizableSpace_tangentOrbit]
-/
#guard_msgs (whitespace := lax) in
#rt_check_soft RoundTrip.V17_53.B_to_A [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_tangentModelOrbitEquiv,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_tangentOrbit,
  Polyfold.GCT.PolyfoldConstruction.continuous_orbitMap_tangentCatProj,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_16]
#rt_check RoundTrip.V17_53.A_core_to_B [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_tangentModelOrbitEquiv,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_tangentOrbit,
  Polyfold.GCT.PolyfoldConstruction.continuous_orbitMap_tangentCatProj,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_16]
#rt_check RoundTrip.V17_53.B_to_A_core [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_tangentModelOrbitEquiv,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_tangentOrbit,
  Polyfold.GCT.PolyfoldConstruction.continuous_orbitMap_tangentCatProj,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_16]
#rt_check RoundTrip.V17_53.main_core_to_B [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_tangentModelOrbitEquiv,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_tangentOrbit,
  Polyfold.GCT.PolyfoldConstruction.continuous_orbitMap_tangentCatProj,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_16]
#rt_check RoundTrip.V17_53.B_to_main_core [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_tangentModelOrbitEquiv,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_tangentOrbit,
  Polyfold.GCT.PolyfoldConstruction.continuous_orbitMap_tangentCatProj,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_16]
#rt_overlap RoundTrip.V17_53.B_to_A [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_tangentModelOrbitEquiv,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_tangentOrbit,
  Polyfold.GCT.PolyfoldConstruction.continuous_orbitMap_tangentCatProj,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_16]
#rt_overlap RoundTrip.V17_53.B_to_A_core [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_tangentModelOrbitEquiv,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_tangentOrbit,
  Polyfold.GCT.PolyfoldConstruction.continuous_orbitMap_tangentCatProj,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_2_16]

end RoundTrip.V17_53
