import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_33
import Polyfold.Examples.EveryUniformizer.Level

set_option maxSynthPendingDepth 3

/-! Round trip for V17_33, second pass (Theorem 17.1.28, 2021 p. 766: `C_1` is a GCT with the
polyfold structure `(F¹, M_{F¹})`, `M_{F¹}(Ψ¹, Ψ'¹) = M(Ψ, Ψ')¹`).

* `A`: the conjunction of the types of the seven theorems of the first pass
  (`isHomeomorph_modelOrbitEquivOne`, `metrizableSpace_levelOne`, `theorem_17_1_28_gct`,
  `isOpenEmbedding_levelOneFunctor`, `theorem_17_1_28`, `levelOne_hasRegularity_iff`,
  `levelOne_hasUniformizers`; universe `0`) and of `theorem_17_1_28_not_every_pair`
  (`Polyfold/Examples/EveryUniformizer/Level.lean`, the main theorem `Amain`).
* `Amain`: there are `C`, a polyfold structure `S` with uniformizers everywhere, and `Ψ ≠ Ψ'` in
  `F(α)` for an object `α` of level `1` with `Ψ¹ = Ψ'¹`, such that no polyfold structure `S₁` on `C¹`
  makes both `M_{S₁}(Ψ¹, Ψ¹) → M(Ψ, Ψ)¹` and `M_{S₁}(Ψ¹, Ψ'¹) → M(Ψ, Ψ')¹` homeomorphisms.
* `not_B`: `B` asks this for every pair `Ψ, Ψ'`; it does not hold as we read it.  The proof
  re-does the counterexample from the non-item lemmas of `Examples/EveryUniformizer/Level`
  (`exists_mem_levelOneF`, `continuous_of_isHomeomorph_levelOneTransEquiv`,
  `not_continuous_harmGauge`).
* `main_to_notB`, `A_to_notB`: `A`'s main theorem refutes `B`.  `B_to_A`, `B_to_main`: ex falso.

**Harness note** (as in the first pass): `B` and `Amain` mention `levelOneGCT` and `levelOneUnif`,
whose bodies reference the banned `metrizableSpace_levelOne`, `isOpenEmbedding_levelOneFunctor`
(and `modelOrbitHomeomorphOne`, built from `isHomeomorph_modelOrbitEquivOne`) directly.  So the
checks use the local `#rt_check_except_defs` (harness `rtCollectSoft` with these three bodies not
unfolded); plain `#rt_check` fails for that reason only (recorded with `#guard_msgs`).
-/

namespace RoundTrip.V17_33_r2
open Polyfold Set Function Topology TopologicalSpace
open Polyfold.GCT.PolyfoldConstruction
open RoundTrip.V17_33 (B)

/-- The new main theorem. -/
def Amain : Prop :=
  type_of% @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_not_every_pair

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_gct.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.levelOne_hasRegularity_iff.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.levelOne_hasUniformizers.{0}) ∧
  Amain

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne.{0},
    @Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne.{0},
    @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_gct.{0},
    @Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor.{0},
    @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28.{0},
    @Polyfold.GCT.PolyfoldConstruction.levelOne_hasRegularity_iff.{0},
    @Polyfold.GCT.PolyfoldConstruction.levelOne_hasUniformizers.{0},
    @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_not_every_pair⟩

section
open EveryUniformizer Polyfold.Examples.OrbifoldSquareInf Polyfold.Examples.Path

/-- `B` does not hold as we read it (from the non-item lemmas). -/
theorem not_B : ¬ B := by
  intro hB
  obtain ⟨-, S₁, hF, hM⟩ := hB _ (gaugeLevel PH harmGauge) (gaugeLevel_hc PH harmGauge)
  have h := exists_mem_levelOneF PH harmGauge h0 false h0_mem_levelSet_one S₁ hF
  have h' := exists_mem_levelOneF PH harmGauge h0 true h0_mem_levelSet_one S₁ hF
  exact not_continuous_harmGauge (continuous_of_isHomeomorph_levelOneTransEquiv PH harmGauge h0
    hpt_harmH_not_mem_levelSet_one S₁ h h' (hM _ _ h h).1 (hM _ _ h h').1)

end

/-- `A`'s main theorem refutes `B`. -/
theorem main_to_notB : Amain → ¬ B := by
  rintro ⟨C, S, hc, Ψ, Ψ', -, ⟨α, hα, hα'⟩, -, -, hno⟩ hB
  obtain ⟨-, S₁, hF, hM⟩ := hB C S hc
  have h : ∃ α, S.levelOneUnif hc Ψ ∈ S₁.F α := ⟨α, by rw [hF α]; exact ⟨Ψ, hα, rfl⟩⟩
  have h' : ∃ α, S.levelOneUnif hc Ψ' ∈ S₁.F α := ⟨α, by rw [hF α]; exact ⟨Ψ', hα', rfl⟩⟩
  exact hno S₁ h h' ⟨(hM Ψ Ψ h h).1, (hM Ψ Ψ' h h').1⟩

theorem A_to_notB : A → ¬ B := fun hA => main_to_notB hA.2.2.2.2.2.2.2

theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- `B → A` only ex falso. -/
theorem B_to_A : B → A := fun h => absurd h not_B

/-- `B → Amain` only ex falso. -/
theorem B_to_main : B → Amain := fun h => absurd h not_B

/-! ### Harness checks -/

open Lean Elab Command in
/-- `#rt_check_except_defs T [nᵢ]`: the harness traversal `rtCollectSoft` with the bodies of
`levelOneGCT`, `levelOneUnif`, `modelOrbitHomeomorphOne` not unfolded (they reference the banned
theorems directly in their fields). -/
elab "#rt_check_except_defs " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let excl : NameSet := [``Polyfold.GCT.PolyfoldConstruction.levelOneGCT,
    ``Polyfold.GCT.PolyfoldConstruction.levelOneUnif,
    ``Polyfold.GCT.PolyfoldConstruction.modelOrbitHomeomorphOne].foldl
      (fun s n => s.insert n) {}
  let (hard, soft) := rtCollectSoft env (roots.toList.map (·, true)) excl {}
  if hard.contains ``sorryAx || soft.contains ``sorryAx then
    throwError "FAIL: {t.getId} contains sorry"
  let banned := bs.getElems.toList.map (·.getId)
  let badHard := banned.filter hard.contains
  unless badHard.isEmpty do
    throwError "FAIL: {t.getId} uses {badHard} outside the listed definitions and proof fields"
  let badSoft := banned.filter fun b => soft.contains b
  logInfo m!"OK: {t.getId} reaches the banned theorems only through the listed definitions and the proof fields of definitions (soft: {badSoft})"

/--
error: rt_check FAIL: RoundTrip.V17_33_r2.not_B uses [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne,
 Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne,
 Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V17_33_r2.not_B [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_gct,
  Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasRegularity_iff,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasUniformizers,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_not_every_pair]
#rt_check_except_defs RoundTrip.V17_33_r2.not_B [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_gct,
  Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasRegularity_iff,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasUniformizers,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_not_every_pair]
#rt_check_except_defs RoundTrip.V17_33_r2.main_to_notB [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_gct,
  Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasRegularity_iff,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasUniformizers,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_not_every_pair]
#rt_check_except_defs RoundTrip.V17_33_r2.A_to_notB [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_gct,
  Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasRegularity_iff,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasUniformizers,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_not_every_pair]
#rt_check_except_defs RoundTrip.V17_33_r2.B_to_A [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_gct,
  Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasRegularity_iff,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasUniformizers,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_not_every_pair]
#rt_check_except_defs RoundTrip.V17_33_r2.B_to_main [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_gct,
  Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasRegularity_iff,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasUniformizers,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_not_every_pair]

#rt_overlap RoundTrip.V17_33_r2.not_B [Polyfold.GCT.PolyfoldConstruction.isHomeomorph_modelOrbitEquivOne,
  Polyfold.GCT.PolyfoldConstruction.metrizableSpace_levelOne,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_gct,
  Polyfold.GCT.PolyfoldConstruction.isOpenEmbedding_levelOneFunctor,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasRegularity_iff,
  Polyfold.GCT.PolyfoldConstruction.levelOne_hasUniformizers,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_28_not_every_pair]

#print axioms RoundTrip.V17_33_r2.not_B

end RoundTrip.V17_33_r2
