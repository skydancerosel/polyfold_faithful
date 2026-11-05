import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_59

open Set Filter Topology Function Module
open scoped ContDiff

noncomputable section

namespace RoundTrip.V3_59
open Polyfold

/-- The project's statement: `proposition_3_73` and `InvData.contDiffOn_inv` (no universe
parameters; `V : Type`).  `InvData` is vocabulary. -/
def A : Prop := type_of% @Polyfold.proposition_3_73 ∧ type_of% @Polyfold.InvData.contDiffOn_inv

theorem A_holds : A := ⟨@Polyfold.proposition_3_73, @Polyfold.InvData.contDiffOn_inv⟩

/-- B's hypotheses give the project's `InvData` for every `j ≥ 1`: hypothesis (3) is used only
through `d_C = 0 ⟺ interior` (`degIndex_eq_zero_iff`). -/
lemma invData_of_hyp {Rn : Type} [NormedAddCommGroup Rn] [NormedSpace ℝ Rn]
    [FiniteDimensional ℝ Rn] {C U : Set Rn} {f : Rn → Rn} (h : Hyp373 Rn C U f) {j : ℕ}
    (hj : 1 ≤ j) : InvData C U f j := by
  obtain ⟨hC, hUrel, hconv, -, hf, hmaps, -, hDf, hdeg⟩ := h
  have hUC : U ⊆ C := by obtain ⟨O, -, rfl⟩ := hUrel; exact inter_subset_right
  refine ⟨hC, hUrel, hconv, hmaps, hj, contDiffOn_infty.1 hf j, fun x hx => hDf x hx,
    fun x hx => ?_⟩
  rw [← degIndex_eq_zero_iff hC (hUC hx), ← degIndex_eq_zero_iff hC (hmaps hx), hdeg x hx]

/-- A ⇒ B, from the conjunct `proposition_3_73` applied for every `j ≥ 1`: the inverses for the
different `j` agree on `f(U)` (`f` is injective on `U`), so the `j = 1` inverse is `C^j` for all
`j`, i.e. `C^∞`. -/
theorem A_to_B : A → B := by
  rintro ⟨h373, -⟩
  intro Rn _ _ _ C U f hyp
  obtain ⟨hrel, hinj, g, hg1, hgf, hfg⟩ := h373 (invData_of_hyp hyp le_rfl)
  refine ⟨hrel, hinj, g, fun y hy => ⟨(hfg y hy).2, (hfg y hy).1⟩, contDiffOn_infty.2 fun j => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact hg1.of_le (by norm_num)
  · obtain ⟨-, -, g', hg', hgf', -⟩ := h373 (invData_of_hyp hyp hj)
    refine hg'.congr fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hgf x hx, hgf' x hx]

#rt_check RoundTrip.V3_59.A_to_B [Polyfold.proposition_3_73, Polyfold.InvData.contDiffOn_inv]

end RoundTrip.V3_59
