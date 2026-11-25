import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_28

set_option maxSynthPendingDepth 3

/-! Round trip for V19_28 (2021 Theorem 19.4.6, p. 885: under properness, `T` second countable or
paracompact is metrizable).  Universes at `0`; the abstract lemmas at `.{0, 0, 0, 1}` (index type
`B.U.Unif : Type 1`, the level at which `theorem_19_4_6_one/two` use them).  `A` =
`theorem_19_4_6_one` ∧ `theorem_19_4_6_two` (properness = (v2), `T` = `natTop hB`) ∧ the two abstract
lemmas.  `B` reads properness as (v1) for every representative `F` and `T` as `generateFrom NatOpen`.
Glue as in V19_29. -/

namespace RoundTrip.V19_28
open Polyfold Polyfold.GroupoidalCategory Filter Topology

def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_4_6_one.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_4_6_two.{0}) ∧
  (type_of% @Polyfold.Chapter19.metrizableSpace_of_orbitCharts_secondCountable.{0, 0, 0, 1}) ∧
  (type_of% @Polyfold.Chapter19.metrizableSpace_of_orbitCharts_paracompact.{0, 0, 0, 1})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_4_6_one.{0},
    @Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_4_6_two.{0},
    @Polyfold.Chapter19.metrizableSpace_of_orbitCharts_secondCountable.{0, 0, 0, 1},
    @Polyfold.Chapter19.metrizableSpace_of_orbitCharts_paracompact.{0, 0, 0, 1}⟩

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

/-- The main pair (Theorem 19.4.6 (1) and (2)). -/
def Main : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_4_6_one.{0}) ∧
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_4_6_two.{0})

theorem main_A_to_B (hA : Main) : B := by
  intro C B F hB hF hv hsp
  rw [V1_iff B hF, B.proposition_19_4_2_one_iff_two hB] at hv
  rw [natT_eq B hB] at hsp ⊢
  rcases hsp with h | h
  · exact hA.1 B hB hv h
  · exact hA.2 B hB hv h

theorem A_to_B : A → B := fun hA => main_A_to_B ⟨hA.1, hA.2.1⟩

theorem main_B_to_A (hB' : B) : Main := by
  refine ⟨fun {C} B hB hv hsc => ?_, fun {C} B hB hv hpc => ?_⟩
  · have hv' := (V1_iff B B.mk_rep).2 ((B.proposition_19_4_2_one_iff_two hB).2 hv)
    have h := hB' C B B.rep hB B.mk_rep hv' (Or.inl (by rw [natT_eq B hB]; exact hsc))
    rwa [natT_eq B hB] at h
  · have hv' := (V1_iff B B.mk_rep).2 ((B.proposition_19_4_2_one_iff_two hB).2 hv)
    have h := hB' C B B.rep hB B.mk_rep hv' (Or.inr (by rw [natT_eq B hB]; exact hpc))
    rwa [natT_eq B hB] at h

/-! The abstract conjuncts, re-proved outright (the project's proofs, from the non-item
`completelyRegularSpace_of_orbitCharts`, `t2Space_of_orbitCharts`, `metrizableSpace_of_locally`);
`B` concerns basic constructions only and cannot give them. -/

section Abstract
variable {Z : Type} [TopologicalSpace Z] {ι : Type 1} {G : ι → Type} [∀ i, Group (G i)]
  [∀ i, Finite (G i)] {O : ι → Type} [∀ i, TopologicalSpace (O i)] [∀ i, MulAction (G i) (O i)]
  [∀ i, ContinuousConstSMul (G i) (O i)] {π : ∀ i, O i → Z}

theorem sc' [∀ i, TopologicalSpace.MetrizableSpace (O i)] [SecondCountableTopology Z]
    (hπ : ∀ i, Chapter19.IsOrbitChart (G i) (π i)) (hcov : ∀ z : Z, ∃ i o, π i o = z)
    (hv : ∀ i o, Chapter19.OrbitChartV2 (π i) o) : TopologicalSpace.MetrizableSpace Z := by
  obtain ⟨h2, h3⟩ := Chapter19.completelyRegularSpace_of_orbitCharts hπ hcov hv
  exact TopologicalSpace.metrizableSpace_of_t3_secondCountable Z

theorem pc' [∀ i, TopologicalSpace.MetrizableSpace (O i)] [ParacompactSpace Z]
    (hπ : ∀ i, Chapter19.IsOrbitChart (G i) (π i)) (hcov : ∀ z : Z, ∃ i o, π i o = z)
    (hv : ∀ i o, Chapter19.OrbitChartV2 (π i) o) : TopologicalSpace.MetrizableSpace Z := by
  have := Chapter19.t2Space_of_orbitCharts hπ hcov hv
  refine metrizableSpace_of_locally fun z => ?_
  obtain ⟨i, o, rfl⟩ := hcov z
  exact ⟨Set.range (π i), (hπ i).isOpen_range, Set.mem_range_self o, (hπ i).metrizableSpace_range⟩

end Abstract

theorem B_to_A : B → A := fun hB' =>
  ⟨(main_B_to_A hB').1, (main_B_to_A hB').2, @sc', @pc'⟩

#rt_check RoundTrip.V19_28.A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_4_6_one,
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_4_6_two,
  Polyfold.Chapter19.metrizableSpace_of_orbitCharts_secondCountable,
  Polyfold.Chapter19.metrizableSpace_of_orbitCharts_paracompact]
#rt_check RoundTrip.V19_28.B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_4_6_one,
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_4_6_two,
  Polyfold.Chapter19.metrizableSpace_of_orbitCharts_secondCountable,
  Polyfold.Chapter19.metrizableSpace_of_orbitCharts_paracompact]
#rt_check RoundTrip.V19_28.main_A_to_B [Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_4_6_one,
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_4_6_two,
  Polyfold.Chapter19.metrizableSpace_of_orbitCharts_secondCountable,
  Polyfold.Chapter19.metrizableSpace_of_orbitCharts_paracompact]
#rt_check RoundTrip.V19_28.main_B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_4_6_one,
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_4_6_two,
  Polyfold.Chapter19.metrizableSpace_of_orbitCharts_secondCountable,
  Polyfold.Chapter19.metrizableSpace_of_orbitCharts_paracompact]
#rt_overlap RoundTrip.V19_28.B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_4_6_one,
  Polyfold.GroupoidalCategory.BasicConstruction.theorem_19_4_6_two,
  Polyfold.Chapter19.metrizableSpace_of_orbitCharts_secondCountable,
  Polyfold.Chapter19.metrizableSpace_of_orbitCharts_paracompact]

end RoundTrip.V19_28
