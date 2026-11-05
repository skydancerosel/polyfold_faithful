import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_7

/-! Round trip for V5_7 (Definition 5.4: compact solution set, weakly proper, proper).

A = the types of the two listed lemmas `StrongBundle.IsProper.isWeaklyProper` (for a continuous
`f`) and `StrongBundle.IsWeaklyProper.isCompact_solutionSet` (universes at `0`); the listed
definitions `AuxLe`, `IsWeaklyProper`, `IsProper` are vocabulary.  B = the project's definitions
are the text's (`IsWeaklyProperB`, `IsProperB`) ∧ "proper ⇒ weakly proper" for sc-smooth sections
∧ "weakly proper ⇒ compact solution set".  The definitional conjuncts are proved outright
(`weaklyProper_iff`, `proper_iff`: `solSetB = solutionSet`, `suppB = closure {¬ IsZeroAt}`,
`NLe = AuxLe`, all definitional). -/

namespace RoundTrip.V5_7
open Polyfold

/-- The project's statement, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.StrongBundle.IsProper.isWeaklyProper.{0, 0} ∧
  type_of% @Polyfold.StrongBundle.IsWeaklyProper.isCompact_solutionSet.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.StrongBundle.IsProper.isWeaklyProper.{0, 0},
    @Polyfold.StrongBundle.IsWeaklyProper.isCompact_solutionSet.{0, 0}⟩

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

theorem weaklyProper_iff (Bd : StrongBundle PX P) (f : X → Y) :
    Bd.IsWeaklyProper f ↔ IsWeaklyProperB Bd f := Iff.rfl

theorem proper_iff (Bd : StrongBundle PX P) (f : X → Y) :
    Bd.IsProper f ↔ IsProperB Bd f := Iff.rfl

end

/-- `A ⇒ B`: the definitions agree outright; the two implications are A's lemmas (an sc-smooth
section is continuous, as a map into `Y[0]`). -/
theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd
  refine ⟨weaklyProper_iff Bd, proper_iff Bd, fun f hf hp => ?_, fun f hw => ?_⟩
  · have hfc : Continuous f := continuousOn_univ.1 hf.2.continuousOn
    exact (weaklyProper_iff Bd f).1 (hA.1 hfc ((proper_iff Bd f).2 hp))
  · exact hA.2 ((weaklyProper_iff Bd f).2 hw)

/-! `B ⇒ A` is not proved: B's "proper ⇒ weakly proper" is stated for sc-smooth sections only,
while A's `IsProper.isWeaklyProper` holds for every continuous `f : X → Y` (not even a section).
B gives A's second conjunct (`B_gives_A_compact`) and A's first conjunct for sc-smooth sections
(`B_gives_A_scSmooth`); the remaining generality is elementary but not a consequence of B. -/

theorem B_gives_A_compact (hB : B) : type_of% @Polyfold.StrongBundle.IsWeaklyProper.isCompact_solutionSet.{0, 0} := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f hw
  exact (hB PX P Bd).2.2.2 f (((hB PX P Bd).1 f).1 hw)

theorem B_gives_A_scSmooth (hB : B) :
    ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
      {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
      {Bd : StrongBundle PX P} {f : X → Y},
      Bd.IsScSmoothSection f → Bd.IsProper f → Bd.IsWeaklyProper f := by
  intro X _ _ _ PX Y _ _ _ P _ _ Bd f hf hp
  exact ((hB PX P Bd).1 f).2 ((hB PX P Bd).2.2.1 f hf (((hB PX P Bd).2.1 f).1 hp))

#rt_check RoundTrip.V5_7.A_to_B [Polyfold.StrongBundle.IsProper.isWeaklyProper,
  Polyfold.StrongBundle.IsWeaklyProper.isCompact_solutionSet]
#rt_check RoundTrip.V5_7.B_gives_A_compact [Polyfold.StrongBundle.IsProper.isWeaklyProper,
  Polyfold.StrongBundle.IsWeaklyProper.isCompact_solutionSet]
#rt_check RoundTrip.V5_7.B_gives_A_scSmooth [Polyfold.StrongBundle.IsProper.isWeaklyProper,
  Polyfold.StrongBundle.IsWeaklyProper.isCompact_solutionSet]

end RoundTrip.V5_7
