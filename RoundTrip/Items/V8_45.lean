import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_45

/-! Round trip for V8_45 (2021 Proposition 8.1.17, p. 371: LUC and SLUC for `TX`).

`A` is the conjunction of the types of the five listed theorems, universes at `0`:
`EpGroupoid.nonEffectivePart_tangent_eq` (`(T𝐗)^T = p⁻¹((𝐗¹)^T)`),
`EpGroupoid.proposition_8_1_17_2021_one` (`X¹` LUC ⇒ `TX` LUC),
`EpGroupoid.proposition_8_1_17_2021_two` (`X` SLUC ⇒ `TX = (TX)⁰` LUC),
`EpGroupoid.isOpenMap_tangentProj_of_subsingleton` and
`EpGroupoid.Examples.proposition_8_1_17_2021_one_point` (no universe parameters).  The first
three carry two hypotheses the text does not state: `X.HasConnectedDenseLevelOneReps` (every
`x ∈ X₁` has a natural representation with `U(x) ∩ X₁` preconnected in `X¹` and dense in `U(x)`)
and `IsOpenMap X.PMor.tangentProj` (`p : T𝐗 → 𝐗¹` open).

* `B → A` (proved): the first two conjuncts are `B`'s (1) with the extra hypotheses dropped;
  the third is `B`'s (1) at `X¹ = (A.lift 1).X` (or `B`'s (2) at level `0`); the point example is
  `B`'s (1) at `pointEpGroupoid` (with the non-item `isLUC_liftOne_point`).  The witness
  `isOpenMap_tangentProj_of_subsingleton` is not a consequence of `B`; re-proved outright.
* `A → B` (not proved): `B` gives neither `HasConnectedDenseLevelOneReps` nor the openness of
  `p`, and `A`'s (2) covers only `(TX)⁰`, while `B`'s (2) is (LUC) for every `(TX)ⁱ`.  The level
  gap is glue (the project's `EP.tangentLiftEpEquiv` transports (LUC) from `T(Xⁱ)` to `(TX)ⁱ`),
  but the two hypotheses are not: the openness of `p` is a Part I fact the project leaves open
  (gap G.8), and `HasConnectedDenseLevelOneReps` is an assumption of the text's Appendix 7.6.4
  (satisfiable, e.g. for the point ep-groupoid; whether it holds for every ep-groupoid is not
  established). -/

namespace RoundTrip.V8_45
open Polyfold Set Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.nonEffectivePart_tangent_eq.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_8_1_17_2021_one.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_8_1_17_2021_two.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isOpenMap_tangentProj_of_subsingleton.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.Examples.proposition_8_1_17_2021_one_point)

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.nonEffectivePart_tangent_eq.{0},
    @Polyfold.EpGroupoid.proposition_8_1_17_2021_one.{0},
    @Polyfold.EpGroupoid.proposition_8_1_17_2021_two.{0},
    @Polyfold.EpGroupoid.isOpenMap_tangentProj_of_subsingleton.{0},
    @Polyfold.EpGroupoid.Examples.proposition_8_1_17_2021_one_point⟩

/-- The witness conjunct, re-proved outright (not a consequence of `B`). -/
theorem isOpenMap_tangentProj_of_subsingleton' {Z : Type} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] [Subsingleton Z] (P : MPolyfold Z) : IsOpenMap P.tangentProj := by
  have : Subsingleton (P.Level 1) := ⟨fun a b => MPolyfold.level_ext (Subsingleton.elim _ _)⟩
  intro s _
  rcases (P.tangentProj '' s).eq_empty_or_nonempty with h | ⟨a, ha⟩
  · rw [h]; exact isOpen_empty
  · have : P.tangentProj '' s = univ := eq_univ_of_forall fun b => Subsingleton.elim a b ▸ ha
    rw [this]; exact isOpen_univ

/-! ### `B → A` -/

theorem B_to_A : B → A := fun hB =>
  ⟨fun X h _ _ => (hB.1 _ _ X h).2, fun X h _ _ => (hB.1 _ _ X h).1,
    fun A h _ _ => (hB.1 _ _ A.X (h 1)).1, @isOpenMap_tangentProj_of_subsingleton',
    (hB.1 Unit Unit EpGroupoid.Examples.pointEpGroupoid EpGroupoid.Examples.isLUC_liftOne_point).1⟩

/-! ### `A → B`: not proved

`A`'s three theorems need `X.HasConnectedDenseLevelOneReps` and `IsOpenMap X.PMor.tangentProj`
(for (2): for every lift `Xⁱ`), which `B`'s premises do not supply. -/

#rt_check RoundTrip.V8_45.B_to_A [Polyfold.EpGroupoid.nonEffectivePart_tangent_eq,
  Polyfold.EpGroupoid.proposition_8_1_17_2021_one, Polyfold.EpGroupoid.proposition_8_1_17_2021_two,
  Polyfold.EpGroupoid.isOpenMap_tangentProj_of_subsingleton,
  Polyfold.EpGroupoid.Examples.proposition_8_1_17_2021_one_point]
#rt_overlap RoundTrip.V8_45.B_to_A [Polyfold.EpGroupoid.nonEffectivePart_tangent_eq,
  Polyfold.EpGroupoid.proposition_8_1_17_2021_one, Polyfold.EpGroupoid.proposition_8_1_17_2021_two,
  Polyfold.EpGroupoid.isOpenMap_tangentProj_of_subsingleton,
  Polyfold.EpGroupoid.Examples.proposition_8_1_17_2021_one_point]

end RoundTrip.V8_45
