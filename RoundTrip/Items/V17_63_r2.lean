import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_63
import Polyfold.Chapter17.EveryUniformizerSub

set_option maxSynthPendingDepth 3

/-! Round trip for V17_63, second pass (Proposition 17.3.6, 2021 p. 786: a subpolyfold `A`
inherits the polyfold structure `(F_A, M)`, `M(Ψ_A, Ψ'_A) = s⁻¹(A_Ψ) ⊆ M(Ψ, Ψ')`).

* `A`: the conjunction of the types of the three theorems of the first pass (`mem_subF_iff`,
  `proposition_17_3_6`, `reflection_subConstruction`; universe `0`) and of
  `proposition_17_3_6_not_every_pair` (`Polyfold/Chapter17/EveryUniformizerSub.lean`, the main
  theorem `Amain`).
* `Amain`: there are `C`, a polyfold structure `S` with uniformizers everywhere, a subpolyfold `A`
  and `Ψ ≠ Ψ'` in `F(α)` for an `α ∈ A` with `Ψ_A = Ψ'_A`, such that no polyfold structure `S_A`
  on `A` makes both `M_{S_A}(Ψ_A, Ψ_A) → s⁻¹(A_Ψ) ⊆ M(Ψ, Ψ)` and
  `M_{S_A}(Ψ_A, Ψ'_A) → s⁻¹(A_Ψ) ⊆ M(Ψ, Ψ')` homeomorphisms.
* `not_B`: `B` asks this for every pair `Ψ, Ψ'`; it does not hold as we read it.  The proof
  re-does the counterexample from the non-item lemmas of `EveryUniformizerSub`
  (`isSubpolyfold_gaugeSub`, `continuous_of_isHomeomorph_restrictTransEquiv`,
  `not_continuous_stepGauge`).  `B`'s `Def1` is the project's `IsSubpolyfold` written out.
* `main_to_notB`, `A_to_notB`: `A`'s main theorem refutes `B`.  `B_to_A`, `B_to_main`: ex falso.
-/

namespace RoundTrip.V17_63_r2
open Polyfold GCT.PolyfoldConstruction Set Function
open RoundTrip.V17_63 (B Def1)

/-- The new main theorem. -/
def Amain : Prop :=
  type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6_not_every_pair

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.mem_subF_iff.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.reflection_subConstruction) ∧
  Amain

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.mem_subF_iff.{0},
    @Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6.{0},
    @Polyfold.GCT.PolyfoldConstruction.reflection_subConstruction,
    @Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6_not_every_pair⟩

/-- From `B`: for `Ψ, Ψ' ∈ F(α)`, `α ∈ A`, both identifications are homeomorphisms. -/
theorem homeos_of_B (hB : B) {C : GCT.{0}} (S : C.PolyfoldConstruction) (A : Set C.Obj)
    (hA : C.toGroupoidStr.IsSaturated A) (hS : S.IsSubpolyfold A) (Ψ Ψ' : S.Unif)
    (p : Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A)) (p' : Ψ'.1.P.IsSubMPolyfold (Ψ'.1.obj ⁻¹' A))
    (α : C.Obj) (hα : α ∈ A) (hΨ : Ψ.1 ∈ S.F α) (hΨ' : Ψ'.1 ∈ S.F α) :
    ∃ (SA : (C.sub A).PolyfoldConstruction)
      (h : ∃ α, GCT.LocalUniformizer.restrict hA p ∈ SA.F α)
      (h' : ∃ α, GCT.LocalUniformizer.restrict hA p' ∈ SA.F α),
      @IsHomeomorph _ _ (SA.topM ⟨_, h⟩ ⟨_, h⟩) _ (S.restrictTransEquiv hA Ψ Ψ p p) ∧
        @IsHomeomorph _ _ (SA.topM ⟨_, h⟩ ⟨_, h'⟩) _ (S.restrictTransEquiv hA Ψ Ψ' p p') := by
  obtain ⟨SA, hF, hM⟩ := hB C S A hA hS
  have h : ∃ α, GCT.LocalUniformizer.restrict hA p ∈ SA.F α :=
    ⟨show (C.sub A).Obj from ⟨α, hα⟩, by
      have e := hF (show (C.sub A).Obj from ⟨α, hα⟩)
      rw [e]; exact ⟨Ψ, hΨ, p, rfl⟩⟩
  have h' : ∃ α, GCT.LocalUniformizer.restrict hA p' ∈ SA.F α :=
    ⟨show (C.sub A).Obj from ⟨α, hα⟩, by
      have e := hF (show (C.sub A).Obj from ⟨α, hα⟩)
      rw [e]; exact ⟨Ψ', hΨ', p', rfl⟩⟩
  obtain ⟨-, H₀, -⟩ := hM Ψ Ψ p p h h
  obtain ⟨-, H₁, -⟩ := hM Ψ Ψ' p p' h h'
  exact ⟨SA, h, h', H₀, H₁⟩

section
open EveryUniformizer

/-- `B` does not hold as we read it (from the non-item lemmas). -/
theorem not_B : ¬ B := by
  intro hB
  obtain ⟨SA, h, h', H₀, H₁⟩ := homeos_of_B hB (gaugeSub stepGauge) posSet isSaturated_posSet
    (isSubpolyfold_gaugeSub stepGauge) (unifAt (rnPolyfold 1) posSet stepGauge false 0)
    (unifAt (rnPolyfold 1) posSet stepGauge true 0) isSubMPolyfold_posSet isSubMPolyfold_posSet
    (fun _ => 1) (show (0 : ℝ) < 1 from one_pos) ⟨false, rfl⟩ ⟨true, rfl⟩
  exact not_continuous_stepGauge
    (continuous_of_isHomeomorph_restrictTransEquiv stepGauge 0 SA h h' H₀ H₁)

end

/-- `A`'s main theorem refutes `B`. -/
theorem main_to_notB : Amain → ¬ B := by
  rintro ⟨C, S, A, hA, Ψ, Ψ', p, p', -, hS, ⟨α, hα, hΨ, hΨ'⟩, -, -, hno⟩ hB
  obtain ⟨SA, h, h', H₀, H₁⟩ := homeos_of_B hB S A hA hS Ψ Ψ' p p' α hα hΨ hΨ'
  exact hno SA h h' ⟨H₀, H₁⟩

theorem A_to_notB : A → ¬ B := fun hA => main_to_notB hA.2.2.2

theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- `B → A` only ex falso. -/
theorem B_to_A : B → A := fun h => absurd h not_B

/-- `B → Amain` only ex falso. -/
theorem B_to_main : B → Amain := fun h => absurd h not_B

#rt_check RoundTrip.V17_63_r2.not_B [Polyfold.GCT.PolyfoldConstruction.mem_subF_iff,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6,
  Polyfold.GCT.PolyfoldConstruction.reflection_subConstruction,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6_not_every_pair]
#rt_check RoundTrip.V17_63_r2.main_to_notB [Polyfold.GCT.PolyfoldConstruction.mem_subF_iff,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6,
  Polyfold.GCT.PolyfoldConstruction.reflection_subConstruction,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6_not_every_pair]
#rt_check RoundTrip.V17_63_r2.A_to_notB [Polyfold.GCT.PolyfoldConstruction.mem_subF_iff,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6,
  Polyfold.GCT.PolyfoldConstruction.reflection_subConstruction,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6_not_every_pair]
#rt_check RoundTrip.V17_63_r2.B_to_A [Polyfold.GCT.PolyfoldConstruction.mem_subF_iff,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6,
  Polyfold.GCT.PolyfoldConstruction.reflection_subConstruction,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6_not_every_pair]
#rt_check RoundTrip.V17_63_r2.B_to_main [Polyfold.GCT.PolyfoldConstruction.mem_subF_iff,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6,
  Polyfold.GCT.PolyfoldConstruction.reflection_subConstruction,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6_not_every_pair]

#rt_overlap RoundTrip.V17_63_r2.not_B [Polyfold.GCT.PolyfoldConstruction.mem_subF_iff,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6,
  Polyfold.GCT.PolyfoldConstruction.reflection_subConstruction,
  Polyfold.GCT.PolyfoldConstruction.proposition_17_3_6_not_every_pair]

#print axioms RoundTrip.V17_63_r2.not_B

end RoundTrip.V17_63_r2
