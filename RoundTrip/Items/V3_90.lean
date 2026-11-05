import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_90

/-!
Round trip for V3_90 (Proposition 3.73 and Lemma 3.77).  `A` is the conjunction of the types of
`Polyfold.InvDataW.injOn`, `Polyfold.InvDataW.hasFDerivWithinAt_inv` and
`Polyfold.InvDataW.contDiffOn_inv`, universes instantiated at `0` (`InvDataW` is vocabulary).

`A` is the inverse function machinery under the *weak* hypotheses `InvDataW U f j`: `U` convex with
unique differentiability, `f` of class `C^j`, `‖Df − 1‖ ≤ 1/2`, and the unique differentiability of
the image `f(U)` **assumed**.  `B` is the quadrant statement: `U` relatively open in a partial
quadrant `C`, `f` smooth, `d_C(x) = d_C(f(x))`, and it **concludes** that `f(U)` is relatively open.

Glue for `A → B`:
* `d_C(x) = d_C(f(x))` gives `x ∈ int C ↔ f(x) ∈ int C` (`degIndex_eq_zero_iff`), so B's
  hypotheses give the project's `InvData C U f j` for every `j ≥ 1`.
* The relative openness of `f(U)` (Lemma 3.74) is **not** in `A`; it is the project lemma
  `InvData.image_relOpen` (not one of the item's declarations).  It gives the unique
  differentiability of `f(U)` (`InvData.uniqueDiffOn_image`), so `InvDataW U f j` holds for all
  `j ≥ 1`.
* Then `A` gives injectivity, `C^j` of `g = InvDataW.inv U f` for every `j` (hence `C^∞`; `g` does
  not depend on `j`), and `Dg(y) = Ring.inverse (Df(g y))`, which is `e⁻¹` for the continuous linear
  equivalence `e` attached to the unit `Df(g y)`.
-/

namespace RoundTrip.V3_90
open Polyfold Set
open scoped ContDiff

/-- The project's statement: the conclusions of the `InvDataW` machinery, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.InvDataW.injOn.{0} ∧ type_of% @Polyfold.InvDataW.hasFDerivWithinAt_inv.{0} ∧
    type_of% @Polyfold.InvDataW.contDiffOn_inv.{0}

theorem A_holds : A :=
  ⟨@Polyfold.InvDataW.injOn.{0}, @Polyfold.InvDataW.hasFDerivWithinAt_inv.{0},
    @Polyfold.InvDataW.contDiffOn_inv.{0}⟩

/-- B's hypotheses give the project's `InvData` (Proposition 3.73's hypotheses) for every
`j ≥ 1`. -/
theorem invData_of_hyp {Rn : Type} [NormedAddCommGroup Rn] [NormedSpace ℝ Rn]
    [FiniteDimensional ℝ Rn] {C U : Set Rn} {f : Rn → Rn} (h : Hyp373 Rn C U f) {j : ℕ}
    (hj : 1 ≤ j) : InvData C U f j := by
  obtain ⟨hC, hrel, hconv, h0U, hsm, hmaps, -, hbd, hdeg⟩ := h
  refine ⟨hC, hrel, hconv, hmaps, hj, hsm.of_le (by exact_mod_cast le_top), hbd, ?_⟩
  intro x hx
  have hUC : U ⊆ C := by obtain ⟨O, -, hU⟩ := hrel; rw [hU]; exact inter_subset_right
  rw [← degIndex_eq_zero_iff hC (hUC hx), ← degIndex_eq_zero_iff hC (hmaps hx), hdeg x hx]

/-- B's hypotheses give the weak hypotheses `InvDataW U f j` for every `j ≥ 1` (the unique
differentiability of `f(U)` from Lemma 3.74, `InvData.image_relOpen`). -/
theorem invDataW_of_hyp {Rn : Type} [NormedAddCommGroup Rn] [NormedSpace ℝ Rn]
    [FiniteDimensional ℝ Rn] {C U : Set Rn} {f : Rn → Rn} (h : Hyp373 Rn C U f) {j : ℕ}
    (hj : 1 ≤ j) : InvDataW U f j :=
  have hI := invData_of_hyp h hj
  ⟨hI.convex, hI.uniqueDiffOn_U, hI.uniqueDiffOn_image, hj, hI.contDiffOn, hI.deriv_bound⟩

theorem A_to_B (hA : A) : B := by
  intro Rn _ _ _ C U f h
  have hW1 : InvDataW U f 1 := invDataW_of_hyp h le_rfl
  refine ⟨(invData_of_hyp h le_rfl).image_relOpen, hA.1 hW1, InvDataW.inv U f,
    fun y hy => ⟨hW1.inv_mem hy, hW1.apply_inv hy⟩, ?_, ?_⟩
  · refine contDiffOn_infty.2 fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact (hA.2.2 hW1).of_le (by norm_num)
    · exact hA.2.2 (invDataW_of_hyp h hn)
  · intro y hy
    have hx : InvDataW.inv U f y ∈ U := hW1.inv_mem hy
    set u := hW1.derivUnit hx with hu
    refine ⟨ContinuousLinearEquiv.unitsEquiv ℝ Rn u, ?_, ?_⟩
    · rw [← hW1.derivUnit_val hx, ← hu]
      exact ContinuousLinearMap.ext fun _ => rfl
    · have h1 := hA.2.1 hW1 hy
      rw [← hW1.derivUnit_val hx, ← hu, Ring.inverse_unit] at h1
      convert h1 using 1
      exact ContinuousLinearMap.ext fun _ => rfl

#rt_check RoundTrip.V3_90.A_to_B [Polyfold.InvDataW.injOn, Polyfold.InvDataW.hasFDerivWithinAt_inv,
  Polyfold.InvDataW.contDiffOn_inv]
#rt_overlap RoundTrip.V3_90.A_to_B [Polyfold.InvDataW.injOn,
  Polyfold.InvDataW.hasFDerivWithinAt_inv, Polyfold.InvDataW.contDiffOn_inv]

end RoundTrip.V3_90
