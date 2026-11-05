import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_17

/-! Round trip for V2_17 (Theorem 2.16: `X`, `X_m` and `X_∞` are metrizable).

`A` is the conjunction of the types of the theorems `Polyfold.theorem_2_16`,
`Polyfold.MPolyfold.metrizableSpace`, `Polyfold.MPolyfold.metrizableSpace_level`,
`Polyfold.MPolyfold.paracompactSpace_level`, `Polyfold.MPolyfold.smoothLevel_topology_eq`,
`Polyfold.MPolyfold.metrizableSpace_smoothLevel` and `Polyfold.MPolyfold.paracompactSpace_subtype`,
all instantiated at universe `0` (B lives in `Type`).  `Polyfold.MPolyfold.SmoothLevel` is a
definition (vocabulary): `X_∞` as the subtype of `⋂ X_m`, the same type B uses.

`A → B`: B's levels carry `P.levelTopology m`, which is the project's instance on `P.Level m`;
B's topology on `X_∞` (the infimum of the topologies induced by the inclusions `X_∞ → X_m`) is the
project's instance by `smoothLevel_topology_eq`.

`B → A`: the conjuncts on `X_m` and `X_∞` are B (the identification of B's topology on `X_∞`
with the project's instance is re-proved here, `smoothTopology_eq`).  "`X` is metrizable" is B at
`m = 0`, transported along the homeomorphism `X ≃ X_0` (`X_0 = X` as sets, and the generators
`φ⁻¹(W)` of the level-0 topology are open in `X`): `isEmbedding_levelZero`.  Paracompactness of
every subset of `X` follows from metrizability of `X`. -/

namespace RoundTrip.V2_17
open Polyfold Set TopologicalSpace

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.theorem_2_16.{0}) ∧ (type_of% @Polyfold.MPolyfold.metrizableSpace.{0}) ∧
    (type_of% @Polyfold.MPolyfold.metrizableSpace_level.{0}) ∧
    (type_of% @Polyfold.MPolyfold.paracompactSpace_level.{0}) ∧
    (type_of% @Polyfold.MPolyfold.smoothLevel_topology_eq.{0}) ∧
    (type_of% @Polyfold.MPolyfold.metrizableSpace_smoothLevel.{0}) ∧
    (type_of% @Polyfold.MPolyfold.paracompactSpace_subtype.{0})

theorem A_holds : A :=
  ⟨@Polyfold.theorem_2_16.{0}, @Polyfold.MPolyfold.metrizableSpace.{0},
    @Polyfold.MPolyfold.metrizableSpace_level.{0}, @Polyfold.MPolyfold.paracompactSpace_level.{0},
    @Polyfold.MPolyfold.smoothLevel_topology_eq.{0},
    @Polyfold.MPolyfold.metrizableSpace_smoothLevel.{0},
    @Polyfold.MPolyfold.paracompactSpace_subtype.{0}⟩

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)

/-- B's topology on `X_∞` is the project's instance. -/
theorem smoothTopology_eq :
    (inferInstance : TopologicalSpace P.SmoothLevel) = smoothTopology P := by
  change TopologicalSpace.induced P.smoothIncl (⨅ m, TopologicalSpace.induced (fun f => f m) _) = _
  rw [induced_iInf]
  simp only [induced_compose]
  rfl

/-- The point `x ∈ X = X_0` as an element of `P.Level 0`. -/
def toLevelZero (x : X) : P.Level 0 :=
  P.levelMk 0 x (by rw [P.levelSet_zero]; exact mem_univ x)

omit [T2Space X] [ParacompactSpace X] in
/-- At level `0` the lift of `φ(x)` is `φ(x)`. -/
theorem levelLift_zero (φ : MChart X) (x : X) : MPolyfold.levelLift φ 0 x = φ x :=
  Function.invFun_eq (f := φ.model.E.toBase 0) ⟨φ x, rfl⟩

theorem continuous_toLevelZero : Continuous (toLevelZero P) := by
  let g : X → P.levelSet 0 := fun x => ⟨x, by rw [P.levelSet_zero]; exact mem_univ x⟩
  have h : @Continuous X (P.levelSet 0) _ (TopologicalSpace.generateFrom (P.levelBasis 0)) g := by
    refine continuous_generateFrom_iff.2 ?_
    rintro s ⟨φ, _, W, hW, rfl⟩
    have : g ⁻¹'
        {x : P.levelSet 0 | (x : X) ∈ φ.source ∧ MPolyfold.levelLift φ 0 (x : X) ∈ W} =
        φ.source ∩ φ ⁻¹' W := by
      ext x
      change (x ∈ φ.source ∧ MPolyfold.levelLift φ 0 x ∈ W) ↔ _
      rw [levelLift_zero]; rfl
    rw [this]
    exact φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source hW
  exact h

/-- `X → X_0` is an embedding (indeed a homeomorphism). -/
theorem isEmbedding_levelZero : Topology.IsEmbedding (toLevelZero P) :=
  Function.LeftInverse.isEmbedding (f := P.levelVal 0) (fun _ => rfl)
    (P.continuous_levelVal 0) (continuous_toLevelZero P)

end Glue

theorem A_to_B : A → B := by
  intro hA X _ _ _ P
  obtain ⟨h216, -, -, -, htop, -, -⟩ := hA
  obtain ⟨-, hlev, hsmooth⟩ := h216 P
  refine ⟨fun m => hlev m, ?_⟩
  have h := htop P
  change (inferInstance : TopologicalSpace P.SmoothLevel) = smoothTopology P at h
  rw [← h]
  exact hsmooth

/-- `X` is metrizable, from B at level `0`. -/
theorem metrizable_of_B (hB : B) {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (P : MPolyfold X) : MetrizableSpace X := by
  have h0 : MetrizableSpace (P.Level 0) := ((hB X P).1 0).1
  exact (isEmbedding_levelZero P).metrizableSpace

theorem B_to_A : B → A := by
  intro hB
  have hsm : ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X),
      MetrizableSpace P.SmoothLevel := by
    intro X _ _ _ P
    have h := (hB X P).2
    rw [← smoothTopology_eq P] at h
    exact h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X _ _ _ P
    exact ⟨metrizable_of_B hB P, fun m => (hB X P).1 m, hsm P⟩
  · intro X _ _ _ P
    exact metrizable_of_B hB P
  · intro X _ _ _ P m
    exact ((hB X P).1 m).1
  · intro X _ _ _ P m
    exact ((hB X P).1 m).2
  · intro X _ _ _ P
    exact smoothTopology_eq P
  · intro X _ _ _ P
    exact hsm P
  · intro X _ _ _ P S
    have := metrizable_of_B hB P
    exact paracompactSpace_of_metrizableSpace S

#rt_check RoundTrip.V2_17.A_to_B [Polyfold.theorem_2_16, Polyfold.MPolyfold.metrizableSpace,
  Polyfold.MPolyfold.metrizableSpace_level, Polyfold.MPolyfold.paracompactSpace_level,
  Polyfold.MPolyfold.smoothLevel_topology_eq, Polyfold.MPolyfold.metrizableSpace_smoothLevel,
  Polyfold.MPolyfold.paracompactSpace_subtype]
#rt_check RoundTrip.V2_17.B_to_A [Polyfold.theorem_2_16, Polyfold.MPolyfold.metrizableSpace,
  Polyfold.MPolyfold.metrizableSpace_level, Polyfold.MPolyfold.paracompactSpace_level,
  Polyfold.MPolyfold.smoothLevel_topology_eq, Polyfold.MPolyfold.metrizableSpace_smoothLevel,
  Polyfold.MPolyfold.paracompactSpace_subtype]
#rt_overlap RoundTrip.V2_17.B_to_A [Polyfold.theorem_2_16, Polyfold.MPolyfold.metrizableSpace,
  Polyfold.MPolyfold.metrizableSpace_level, Polyfold.MPolyfold.paracompactSpace_level,
  Polyfold.MPolyfold.smoothLevel_topology_eq, Polyfold.MPolyfold.metrizableSpace_smoothLevel,
  Polyfold.MPolyfold.paracompactSpace_subtype]

end RoundTrip.V2_17
