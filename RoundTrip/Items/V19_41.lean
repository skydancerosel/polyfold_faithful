import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V19_41

set_option maxSynthPendingDepth 3

/-! Round trip for V19_41 (2021 Proposition 19.5.11, p. 890: (ZHOU) of a basic construction gives
(SLUC) and (SLR)).

`A` is the conjunction of the types of `BasicConstruction.proposition_19_5_11` (main conjunct),
`EP.theorem_7_4_13_all_of_isZhou` and `EP.theorem_7_4_24_all_of_isZhou`, all at universe `0`.

* The main conjunct assumes `T` metrizable (`MetrizableSpace C.OrbitSpace`, the standing
  assumption of §19.5 in the project's reading) and concludes (SLUC), (SLR) and also the level-0
  forms (LUC), (LR).  `B` has no metrizability hypothesis and concludes (SLUC), (SLR).
* `B_to_A`: (SLUC)/(SLR) from `B`; (LUC)/(LR) from the level-0 cases of (SLUC)/(SLR) (every class
  is a level-0 class, `levelSet_zero`; `(G ⋉ O)⁰ = G ⋉ O` by `rfl`; `isLUCAt_iff`,
  `isLRAt_of_isLRAt`).  The two Chapter 7 conjuncts are about arbitrary ep-groupoids, outside
  `B`; they are re-proved outright from the (non-item) `theorem_7_4_13_all` /
  `theorem_7_4_24_all` with the Part I facts `denseSmoothTangent`, `smoothRegular`.
* `A_to_B` is not proved: `A`'s route to the (ZHOU) of every `G ⋉ O` goes through the polyfold
  structure `(S, F, M)` (Proposition 19.5.7), which needs `T` metrizable; `B` does not supply it.
-/

namespace RoundTrip.V19_41
open Polyfold

def A : Prop :=
  (type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_11.{0}) ∧
  (type_of% @Polyfold.EP.theorem_7_4_13_all_of_isZhou.{0}) ∧
  (type_of% @Polyfold.EP.theorem_7_4_24_all_of_isZhou.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_11.{0},
    @Polyfold.EP.theorem_7_4_13_all_of_isZhou.{0}, @Polyfold.EP.theorem_7_4_24_all_of_isZhou.{0}⟩

/-- `B` gives the main conjunct of `A` (which has the extra hypothesis `hm` and the extra
level-0 conclusions). -/
theorem main_B_to_A : B →
    type_of% @Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_11.{0} := by
  intro hBB C Bc hB _hm hZ
  obtain ⟨hS, hR⟩ := hBB C Bc hB hZ
  have hpt : ∀ z, Bc.IsLevelClass 0 z := fun z => by
    obtain ⟨α, hα, Ψ, hΨ⟩ := hB z
    obtain ⟨o, ho⟩ := Bc.U.isAt α Ψ hΨ
    exact ⟨⟨Ψ, α, hΨ⟩, o, by rw [MPolyfold.levelSet_zero]; trivial,
      by change C.π (Ψ.obj o) = z; rw [ho, hα]⟩
  refine ⟨hS, hR, fun z => ?_, fun z => ?_⟩
  · obtain ⟨α, Ψ, hΨ, p, hα, hp, R, hRL⟩ := hS 0 z (hpt z)
    exact ⟨α, Ψ, hΨ, p, hα, hp, (Ψ.isLUCAt_iff p).2 ⟨R, hRL⟩⟩
  · obtain ⟨α, Ψ, hΨ, p, hα, hp, hL⟩ := hR 0 z (hpt z)
    exact ⟨α, Ψ, hΨ, p, hα, hp, Ψ.isLRAt_of_isLRAt hL⟩

theorem B_to_A : B → A := fun hBB =>
  ⟨main_B_to_A hBB,
    fun A hZ => A.theorem_7_4_13_all hZ A.X.PObj.denseSmoothTangent
      fun i => (A.lift i).X.PObj.smoothRegular,
    fun A hZ => A.theorem_7_4_24_all hZ A.X.PObj.denseSmoothTangent
      fun i => (A.lift i).X.PObj.smoothRegular⟩

#rt_check RoundTrip.V19_41.main_B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_11,
  Polyfold.EP.theorem_7_4_13_all_of_isZhou, Polyfold.EP.theorem_7_4_24_all_of_isZhou]
#rt_check RoundTrip.V19_41.B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_11,
  Polyfold.EP.theorem_7_4_13_all_of_isZhou, Polyfold.EP.theorem_7_4_24_all_of_isZhou]
#rt_overlap RoundTrip.V19_41.B_to_A [Polyfold.GroupoidalCategory.BasicConstruction.proposition_19_5_11,
  Polyfold.EP.theorem_7_4_13_all_of_isZhou, Polyfold.EP.theorem_7_4_24_all_of_isZhou]

end RoundTrip.V19_41
