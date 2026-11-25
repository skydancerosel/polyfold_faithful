import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V16_56

set_option maxSynthPendingDepth 3

/-! Round trip for V16_56 (2021 Proposition 16.3.16 (2), p. 728; 2017: Proposition 16.5 (2)).

`A` is the conjunction of the types of `StrongPolyfoldBundle.proposition_16_3_16_two` (the main
conjunct: the statement as printed, mixed convergence in any model), `mixedTendsto_iff_forall`
(model independence of Definition 16.3.14) and `proposition_16_3_16_two_of_mem` (the inequality
with mixed convergence read in one structure `S` whose `normOf n` is a reflexive auxiliary norm),
at universe `0`.

* `A_to_B`: the main conjunct, with `B`'s extra hypotheses `y_k, y₀ ∈ Y_{0,1}` unused.
* `B_to_A`: the main conjunct from `B`; `B`'s hypotheses `y_k, y₀ ∈ Y_{0,1}` follow from mixed
  convergence (the representatives `w_k, w₀` give `y_k = Γ(|w_k|) ∈ Y_{0,1}`).  The two other
  conjuncts are not consequences of `B`: `mixedTendsto_iff_forall` is a statement about the
  notion (not mentioned by `B`), and `proposition_16_3_16_two_of_mem` assumes neither
  `⟦S⟧ = c` for a bundle with reflexive `1`-fibres nor `S.A.E.HasReflexiveFibers` (an ep-level
  reflexive auxiliary norm does not contain that), so `B` does not apply to it.  Both are re-proved
  outright from non-item lemmas (the project's short proofs: `mixedTendstoIn_of_equiv`,
  `HasReflexiveFibers.of_mem`, `theorem_12_2_11_exists`, `IsReflexiveAuxNorm.le_liminf`). -/

namespace RoundTrip.V16_56
open Polyfold Filter StrongPolyfoldBundle StrongPolyfoldBundleStructure

def A : Prop :=
  (type_of% @Polyfold.StrongPolyfoldBundle.proposition_16_3_16_two.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.mixedTendsto_iff_forall.{0}) ∧
  (type_of% @Polyfold.StrongPolyfoldBundle.proposition_16_3_16_two_of_mem.{0})

theorem A_holds : A :=
  ⟨@Polyfold.StrongPolyfoldBundle.proposition_16_3_16_two.{0},
    @Polyfold.StrongPolyfoldBundle.mixedTendsto_iff_forall.{0},
    @Polyfold.StrongPolyfoldBundle.proposition_16_3_16_two_of_mem.{0}⟩

/-- Mixed convergence gives `y_k ∈ Y_{0,1}` and `y₀ ∈ Y_{0,1}`. -/
theorem mem_Y01_of_mixedTendsto {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]
    {p : Y → Z} {c : StrongPolyfoldBundle p} {y : ℕ → Y} {y₀ : Y} (hm : c.MixedTendsto y y₀) :
    (∀ k, y k ∈ c.Y01) ∧ y₀ ∈ c.Y01 := by
  obtain ⟨S, hS, -, -, w, w₀, hw, hw₀, -⟩ := hm
  rw [c.Y01_eq hS]
  exact ⟨fun k => ⟨w k, hw k⟩, ⟨w₀, hw₀⟩⟩

/-- The main conjunct gives `B`. -/
theorem Amain_to_B :
    (type_of% @Polyfold.StrongPolyfoldBundle.proposition_16_3_16_two.{0}) → B := by
  intro h Y Z _ _ p c hc n hn y y₀ _ _ hm
  exact h hc hn hm

/-- `B` gives the main conjunct. -/
theorem B_to_Amain : B →
    (type_of% @Polyfold.StrongPolyfoldBundle.proposition_16_3_16_two.{0}) := by
  intro hB Y Z _ _ p c hc n hn y y₀ hm
  exact hB c hc n hn y y₀ (mem_Y01_of_mixedTendsto hm).1 (mem_Y01_of_mixedTendsto hm).2 hm

theorem A_to_B : A → B := fun h => Amain_to_B h.1

/-- `mixedTendsto_iff_forall`, re-proved (the project's proof). -/
theorem mixedTendsto_iff_forall' : type_of% @Polyfold.StrongPolyfoldBundle.mixedTendsto_iff_forall.{0} := by
  intro Y Z _ _ p c hc y y₀
  refine ⟨fun hm S hS => ?_, fun h => ?_⟩
  · obtain ⟨S₀, hS₀, -, -, hm⟩ := hm
    exact mixedTendstoIn_of_equiv (Quotient.exact (hS₀.trans hS.symm)) (hc.of_mem hS) hm
  · obtain ⟨S, hS, hB⟩ := hc
    obtain ⟨N, hN⟩ := S.A.E.theorem_12_2_11_exists S.paracompact hB
    exact ⟨S, hS, hB, ⟨N, hN⟩, h S hS⟩

/-- `proposition_16_3_16_two_of_mem`, re-proved (the project's proof). -/
theorem proposition_16_3_16_two_of_mem' :
    type_of% @Polyfold.StrongPolyfoldBundle.proposition_16_3_16_two_of_mem.{0} := by
  intro Y Z _ _ p n S hN y y₀ hm
  obtain ⟨w, w₀, hw, hw₀, hm⟩ := hm
  have h := hN.le_liminf w w₀ hm
  simp only [normOf, hw, hw₀] at h
  exact h

theorem B_to_A : B → A := fun hB =>
  ⟨B_to_Amain hB, mixedTendsto_iff_forall', proposition_16_3_16_two_of_mem'⟩

#rt_check RoundTrip.V16_56.A_to_B [Polyfold.StrongPolyfoldBundle.proposition_16_3_16_two,
  Polyfold.StrongPolyfoldBundle.mixedTendsto_iff_forall,
  Polyfold.StrongPolyfoldBundle.proposition_16_3_16_two_of_mem]
#rt_check RoundTrip.V16_56.B_to_A [Polyfold.StrongPolyfoldBundle.proposition_16_3_16_two,
  Polyfold.StrongPolyfoldBundle.mixedTendsto_iff_forall,
  Polyfold.StrongPolyfoldBundle.proposition_16_3_16_two_of_mem]
#rt_check RoundTrip.V16_56.Amain_to_B [Polyfold.StrongPolyfoldBundle.proposition_16_3_16_two,
  Polyfold.StrongPolyfoldBundle.mixedTendsto_iff_forall,
  Polyfold.StrongPolyfoldBundle.proposition_16_3_16_two_of_mem]
#rt_check RoundTrip.V16_56.B_to_Amain [Polyfold.StrongPolyfoldBundle.proposition_16_3_16_two,
  Polyfold.StrongPolyfoldBundle.mixedTendsto_iff_forall,
  Polyfold.StrongPolyfoldBundle.proposition_16_3_16_two_of_mem]
#rt_overlap RoundTrip.V16_56.B_to_A [Polyfold.StrongPolyfoldBundle.proposition_16_3_16_two,
  Polyfold.StrongPolyfoldBundle.mixedTendsto_iff_forall,
  Polyfold.StrongPolyfoldBundle.proposition_16_3_16_two_of_mem]

end RoundTrip.V16_56
