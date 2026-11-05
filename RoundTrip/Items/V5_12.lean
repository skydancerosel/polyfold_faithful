import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_12

/-!
Round trip for V5_12 (Theorem 5.7).  `A` is the conjunction of the types of `Polyfold.theorem_5_7`,
`Polyfold.MPolyfold.tendsto_smoothLevel_iff`, `Polyfold.MPolyfold.smoothLevel_topology_eq` and
`Polyfold.MPolyfold.metrizableSpace_smoothLevel`, universes instantiated at `0`.

Glue for `A → B`: B's own topology `smoothTopology PX` on `X_∞` (the infimum of the topologies
induced by `X_∞ → X_m`) is the project's instance by A's conjunct `smoothLevel_topology_eq`;
`solutionSet P f` is `{x | IsZeroAt P f x}` by definition; B's tameness hypothesis is not needed.

`B → A` is proved only for tame `X` (`B_to_A_tame`): A's `theorem_5_7` has no tameness hypothesis,
and B says nothing about non-tame M-polyfolds.  The remaining conjuncts of A are facts about the
project's chosen topology on `X_∞` (convergence = convergence on each level, the infimum form,
metrizability), which B does not state.
-/

/-! **Refresh 2026-11-02** (HEAD after the germ reading of Definition 3.11 and the notions built
on it).
theorem_5_7 and B now both use the germ-reading IsScFredholmSection; theorem_5_7 still drops the
text's tameness of X, the topology conjuncts are unchanged. Result unchanged: A ⇒ B proved (uses
A's smoothLevel_topology_eq), B ⇒ A only for tame X (B_to_A_tame).
-/

namespace RoundTrip.V5_12
open Polyfold

/-- The project's statement, universes `0`. -/
def A : Prop :=
  type_of% @Polyfold.theorem_5_7.{0, 0} ∧
    type_of% @Polyfold.MPolyfold.tendsto_smoothLevel_iff.{0} ∧
    type_of% @Polyfold.MPolyfold.smoothLevel_topology_eq.{0} ∧
    type_of% @Polyfold.MPolyfold.metrizableSpace_smoothLevel.{0}

theorem A_holds : A :=
  ⟨@Polyfold.theorem_5_7.{0, 0}, @Polyfold.MPolyfold.tendsto_smoothLevel_iff.{0},
    @Polyfold.MPolyfold.smoothLevel_topology_eq.{0},
    @Polyfold.MPolyfold.metrizableSpace_smoothLevel.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨h57, -, htop, -⟩ X _ _ _ PX Y _ _ _ P _ _ Bd f _ hf hS
  obtain ⟨hreg, hK⟩ := h57 hf hS
  refine ⟨hreg, ?_⟩
  have e : smoothTopology PX = (inferInstance : TopologicalSpace PX.SmoothLevel) :=
    (htop (P := PX)).symm
  rw [e]
  exact hK

/-- B gives A's `theorem_5_7` for tame `X`. -/
theorem B_to_A_tame : B →
    ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
      {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {Bd : StrongBundle PX P}
      {f : X → Y}, PX.IsTame → Bd.IsScFredholmSection f → IsCompact (solutionSet P f) →
      solutionSet P f ⊆ PX.smoothSet ∧
        IsCompact {x : PX.SmoothLevel | PX.smoothVal x ∈ solutionSet P f} := by
  intro hB X _ _ _ PX Y _ _ _ P _ _ Bd f hX hf hS
  obtain ⟨hreg, hK⟩ := hB PX P Bd f hX hf hS
  refine ⟨hreg, ?_⟩
  -- the project's instance is induced by `X_∞ → ∏_m X_m`; B's is the infimum over `m`
  have e : smoothTopology PX = (inferInstance : TopologicalSpace PX.SmoothLevel) := by
    unfold smoothTopology
    change _ = TopologicalSpace.induced PX.smoothIncl
      (⨅ m, TopologicalSpace.induced (fun g : ∀ k, PX.Level k => g m) _)
    rw [induced_iInf]
    simp only [induced_compose]
    rfl
  rw [e] at hK
  exact hK

#rt_check RoundTrip.V5_12.A_to_B [Polyfold.theorem_5_7, Polyfold.MPolyfold.tendsto_smoothLevel_iff,
  Polyfold.MPolyfold.smoothLevel_topology_eq, Polyfold.MPolyfold.metrizableSpace_smoothLevel]
#rt_check RoundTrip.V5_12.B_to_A_tame [Polyfold.theorem_5_7,
  Polyfold.MPolyfold.tendsto_smoothLevel_iff, Polyfold.MPolyfold.smoothLevel_topology_eq,
  Polyfold.MPolyfold.metrizableSpace_smoothLevel]

end RoundTrip.V5_12
