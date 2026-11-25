import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V16_57

set_option maxSynthPendingDepth 3

/-! Round trip for V16_57 (2021 Theorem 16.3.17 (1), p. 728; 2017: Theorem 16.4 (1)).

The item lists the definition `IsAuxNormBoundary` (vocabulary, used by `B` as well) and the
theorems `theorem_16_3_17_one` (main conjunct), `mem_boundary_iff` (the points of `Y_{0,1}` over
`∂Z` are the `Γ(|e|)` with `P(e) ∈ ∂X`), `IsAuxNorm.isAuxNormBoundary` (an auxiliary norm restricts
to one over `∂Z`) and `theorem_16_3_17_one_witness` (the hypothesis of (1) can be met).  `A` is the
conjunction of the types of the four theorems, at universe `0`.

`c.IsTame` is by definition `c.polyfold.IsTame` (Definition 16.3.5 (1)), so the main conjunct and
`B` are the same statement.  The three side conjuncts are not consequences of `B`; they are
re-proved outright from non-item lemmas (`PolyfoldClass.mem_boundary_iff`, `p_Γ`,
`IsAuxNorm.isAuxNormOn`, `proposition_16_3_10`). -/

namespace RoundTrip.V16_57
open Polyfold StrongPolyfoldBundle StrongPolyfoldBundleStructure

def A : Prop :=
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_3_17_one.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.mem_boundary_iff.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.IsAuxNorm.isAuxNormBoundary.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_3_17_one_witness.{0})

theorem A_holds : A :=
  ⟨@Polyfold.StrongPolyfoldBundle.theorem_16_3_17_one.{0},
    @Polyfold.StrongPolyfoldBundle.mem_boundary_iff.{0},
    @Polyfold.StrongPolyfoldBundle.IsAuxNorm.isAuxNormBoundary.{0},
    @Polyfold.StrongPolyfoldBundle.theorem_16_3_17_one_witness.{0}⟩

theorem Amain_to_B : (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_3_17_one.{0}) → B := by
  intro h Y Z _ _ p c hc n hn
  exact h hc hn

theorem B_to_Amain : B → (type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_3_17_one.{0}) := by
  intro hB Y Z _ _ p c hc n hn
  exact hB c hc n hn

theorem A_to_B : A → B := fun h => Amain_to_B h.1

theorem mem_boundary_iff' : type_of% @Polyfold.StrongPolyfoldBundle.mem_boundary_iff.{0} := by
  intro Y Z _ _ p c S hS e
  rw [← hS]
  exact PolyfoldClass.mem_boundary_iff _ S.toPolyfoldStructure rfl
    (S.p_Γ (S.A.E.toEpGroupoid.π (S.A.B.oneVal e))).symm

theorem isAuxNormBoundary' :
    type_of% @Polyfold.StrongPolyfoldBundle.IsAuxNorm.isAuxNormBoundary.{0} :=
  fun hn S hS => (hn S hS).isAuxNormOn _

theorem witness' : type_of% @Polyfold.StrongPolyfoldBundle.theorem_16_3_17_one_witness.{0} := by
  intro Y Z _ _ p c
  obtain ⟨n, hn⟩ := c.proposition_16_3_10
  exact ⟨n, isAuxNormBoundary' hn⟩

theorem B_to_A : B → A := fun hB =>
  ⟨B_to_Amain hB, mem_boundary_iff', isAuxNormBoundary', witness'⟩

#rt_check RoundTrip.V16_57.A_to_B [Polyfold.StrongPolyfoldBundle.theorem_16_3_17_one,
  Polyfold.StrongPolyfoldBundle.mem_boundary_iff,
  Polyfold.StrongPolyfoldBundle.IsAuxNorm.isAuxNormBoundary,
  Polyfold.StrongPolyfoldBundle.theorem_16_3_17_one_witness]
#rt_check RoundTrip.V16_57.B_to_A [Polyfold.StrongPolyfoldBundle.theorem_16_3_17_one,
  Polyfold.StrongPolyfoldBundle.mem_boundary_iff,
  Polyfold.StrongPolyfoldBundle.IsAuxNorm.isAuxNormBoundary,
  Polyfold.StrongPolyfoldBundle.theorem_16_3_17_one_witness]
#rt_check RoundTrip.V16_57.Amain_to_B [Polyfold.StrongPolyfoldBundle.theorem_16_3_17_one,
  Polyfold.StrongPolyfoldBundle.mem_boundary_iff,
  Polyfold.StrongPolyfoldBundle.IsAuxNorm.isAuxNormBoundary,
  Polyfold.StrongPolyfoldBundle.theorem_16_3_17_one_witness]
#rt_check RoundTrip.V16_57.B_to_Amain [Polyfold.StrongPolyfoldBundle.theorem_16_3_17_one,
  Polyfold.StrongPolyfoldBundle.mem_boundary_iff,
  Polyfold.StrongPolyfoldBundle.IsAuxNorm.isAuxNormBoundary,
  Polyfold.StrongPolyfoldBundle.theorem_16_3_17_one_witness]
#rt_overlap RoundTrip.V16_57.B_to_A [Polyfold.StrongPolyfoldBundle.theorem_16_3_17_one,
  Polyfold.StrongPolyfoldBundle.mem_boundary_iff,
  Polyfold.StrongPolyfoldBundle.IsAuxNorm.isAuxNormBoundary,
  Polyfold.StrongPolyfoldBundle.theorem_16_3_17_one_witness]

end RoundTrip.V16_57
