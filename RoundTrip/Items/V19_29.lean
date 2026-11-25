import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_29

set_option maxSynthPendingDepth 3

/-! Round trip for V19_29 (2021 Proposition 19.4.7, p. 885: `T` is metrizable iff properness holds
and `T` is paracompact).  Universes at `0`; the abstract lemma
`paracompact_and_orbitChartV2_of_metrizableSpace` at `.{0, 0, 0, 1}` (index type `B.U.Unif : Type 1`,
the level at which `proposition_19_4_7` uses it).  `A` = `proposition_19_4_7` (properness = (v2),
`T` = `natTop hB`) ∧ the abstract lemma.  `B` reads properness as (v1) for every representative `F`
and `T` as `generateFrom NatOpen`.  Glue: `natT = natTop` under `HasClassUniformizers`;
`V1 F ↔ PropernessV1` (`T^F_{Ψ,Ψ'}` is the topology of `B.M`, Lemma 19.3.1); `PropernessV1 ↔
PropernessV2` (`proposition_19_4_2_one_iff_two`, not an item theorem here). -/

namespace RoundTrip.V19_29
open Polyfold Polyfold.GroupoidalCategory Filter Topology

def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_7.{0}) ∧
  (type_of% @Polyfold.Chapter19.paracompact_and_orbitChartV2_of_metrizableSpace.{0, 0, 0, 1})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_7.{0},
    @Polyfold.Chapter19.paracompact_and_orbitChartV2_of_metrizableSpace.{0, 0, 0, 1}⟩

theorem natT_eq {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    (hB : B.U.HasClassUniformizers) : natT B.U = B.natTop hB :=
  TopologicalSpace.generateFrom_setOfPred_isOpen (B.natTop hB)

/-- `T^F_{Ψ,Ψ'}` is the topology of `B.M Ψ Ψ'` for a representative `F`. -/
theorem topology_eq {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    {F : B.U.TransitionData} (hF : (⟦F⟧ : B.U.TransitionConstruction) = B.𝓕)
    (Ψ Ψ' : B.U.Unif) : F.topology Ψ Ψ' = B.rep.topology Ψ Ψ' :=
  TopologicalSpace.ext (funext fun _ => propext (B.isOpen_M_iff hF).symm)

theorem tendsto_iff_of_eq {X : Type} {t₁ t₂ : TopologicalSpace X} (h : t₁ = t₂) (f : ℕ → X)
    (x : X) : @Tendsto ℕ X f atTop (@nhds X t₁ x) ↔ @Tendsto ℕ X f atTop (@nhds X t₂ x) := by
  subst h; rfl

theorem V1_iff {C : GroupoidalCategory.{0}} (B : C.BasicConstruction)
    {F : B.U.TransitionData} (hF : (⟦F⟧ : B.U.TransitionConstruction) = B.𝓕) :
    V1 F ↔ B.PropernessV1 := by
  constructor
  · intro hv Ψ o
    obtain ⟨W, hWo, hoW, hW⟩ := hv Ψ o
    refine ⟨W, hWo, hoW, fun Ψ' h hs p hp => ?_⟩
    obtain ⟨φ, x, hφ, hx⟩ := hW Ψ' h hs ⟨p, hp⟩
    exact ⟨φ, hφ, x, (tendsto_iff_of_eq (topology_eq B hF Ψ Ψ') _ _).1 hx⟩
  · intro hv Ψ o
    obtain ⟨W, hWo, hoW, hW⟩ := hv Ψ o
    refine ⟨W, hWo, hoW, fun Ψ' h hs ⟨p, hp⟩ => ?_⟩
    obtain ⟨φ, hφ, x, hx⟩ := hW Ψ' h hs p hp
    exact ⟨φ, x, hφ, (tendsto_iff_of_eq (topology_eq B hF Ψ Ψ') _ _).2 hx⟩

theorem main_A_to_B
    (hA : type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_7.{0}) :
    B := by
  intro C B F hB hF
  rw [natT_eq B hB, V1_iff B hF, B.proposition_19_4_2_one_iff_two hB]
  exact hA B hB

theorem A_to_B : A → B := fun hA => main_A_to_B hA.1

theorem main_B_to_A (hB' : B) :
    type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_7.{0} := by
  intro C B hB
  have h := hB' C B B.rep hB B.mk_rep
  rwa [natT_eq B hB, V1_iff B B.mk_rep, B.proposition_19_4_2_one_iff_two hB] at h

/-- The abstract conjunct, re-proved outright (the project's two-line proof, Mathlib's
`paracompactSpace_of_metrizableSpace` and the non-item `IsOrbitChart.orbitChartV2_of_regularSpace`);
`B` concerns basic constructions only and cannot give it. -/
theorem abstract' {Z : Type} [TopologicalSpace Z] {ι : Type 1} {G : ι → Type}
    [∀ i, Group (G i)] {O : ι → Type} [∀ i, TopologicalSpace (O i)] [∀ i, MulAction (G i) (O i)]
    {π : ∀ i, O i → Z} [TopologicalSpace.MetrizableSpace Z]
    (hπ : ∀ i, Chapter19.IsOrbitChart (G i) (π i)) :
    ParacompactSpace Z ∧ ∀ i o, Chapter19.OrbitChartV2 (π i) o :=
  ⟨paracompactSpace_of_metrizableSpace Z, fun i o => (hπ i).orbitChartV2_of_regularSpace o⟩

theorem B_to_A : B → A := fun hB' => ⟨main_B_to_A hB', @abstract'⟩

#rt_check RoundTrip.V19_29.A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_7,
  Polyfold.Chapter19.paracompact_and_orbitChartV2_of_metrizableSpace]
#rt_check RoundTrip.V19_29.B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_7,
  Polyfold.Chapter19.paracompact_and_orbitChartV2_of_metrizableSpace]
#rt_check RoundTrip.V19_29.main_A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_7,
  Polyfold.Chapter19.paracompact_and_orbitChartV2_of_metrizableSpace]
#rt_check RoundTrip.V19_29.main_B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_7,
  Polyfold.Chapter19.paracompact_and_orbitChartV2_of_metrizableSpace]
#rt_overlap RoundTrip.V19_29.B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_4_7,
  Polyfold.Chapter19.paracompact_and_orbitChartV2_of_metrizableSpace]

end RoundTrip.V19_29
