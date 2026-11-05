import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_37

/-!
Round trip for V3_37 (Lemma 3.42: solutions of the push-forward are on level 1).

`A` is the type of `Polyfold.StabilityData.lemma_3_42` (no universe parameters;
`StabilityData.toShiftedBasicData` is a definition, vocabulary only): for the project's own
coordinate change of Theorem 3.38 (`𝒮 : StabilityData`, `pushMap₀ f = Φ_*(f + s)` on the germ
`pushGerm₀`), for every `ε > 0` there is `r > 0` such that every zero `x` with `|x|₀ < r` has its
fibre component on level `1` with `|·|₁ < ε`.  This is the hypothesis `hreg` of the project's
Theorem 3.43; the identification `w = δ(a)` is done there by uniqueness (`ShiftedBasicData.eq_δ`).

Neither direction is proved.
* `zeros_eq_δ_of_A`: in A's own setting (`𝒟 = 𝒮.toShiftedBasicData`), A plus the project's
  fixed-point uniqueness (`eq_δ`) gives B's first clause (zeros near `0` are `(a, ι δ(a))`), so the
  difference in *form* is glue; the difference in *scope* below is not.
* `A → B` fails genuinely: B quantifies over *every* strong bundle isomorphism `Φ` with `φ(0) = 0`
  (and every basic germ `g₁` agreeing with `Φ_*f` on level 1, every representative `δ`), A is about
  the one explicit linear coordinate change `(split₀, fiber₀)` of `StabilityData`.  For a general
  `Φ` the regularity of zeros has to be re-derived (Theorem 3.40 for `f + s` and the level-1
  continuity of `φ`).  Also the conclusions differ in form: A gives "zeros are on level 1 and small
  there", B gives "zeros are `(a, δ(a))`" plus `|δ(a)|₀ ≤ τ'₀` for small `a`; passing from A's form
  to B's needs the uniqueness of the fixed point of the contraction `g₁` and continuity of `δ`.
* `B → A` is believed true but not proved: instantiating B at the project's coordinate change
  requires the transport glue of V3_34 (`P ≅ ℝ^{n}`, `P × C ≅ ℝ^{n'}`, `Q × Z ≅ ℝ^{N'}`, the basic
  germ and the partial quadrant transported, `(split₀, fiber₀)` as an `IsStrongBundleIso`, B's
  `IsSolGerm` for `𝒞.sol` via Theorem 3.33), then `w₁ = δ(a)` with `δ` continuous into `W'₁` at `0`
  gives A's smallness on level 1.  Too heavy for this audit's budget.
-/

namespace RoundTrip.V3_37
open Polyfold

/-- The project's statement: Lemma 3.42 for the coordinate change of Theorem 3.38. -/
def A : Prop := type_of% @Polyfold.StabilityData.lemma_3_42

theorem A_holds : A := @Polyfold.StabilityData.lemma_3_42

/-- **A gives B's first clause in A's own setting**: for the project's coordinate change
(`𝒟 = 𝒮.toShiftedBasicData`), zeros `x = (a, w)` of `g` near `0` are `(a, ι δ(a))` with `a` in the
solution region.  From A (level-1 regularity) and the uniqueness of the fixed point
(`ShiftedBasicData.eq_δ`); this is the step the project performs inside Theorem 3.43. -/
theorem zeros_eq_δ_of_A (hA : A) {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {W : ScBanach} {Ct : Set P} (𝒮 : StabilityData Ct W) {Q : Type}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    {f : P × W.lvl 0 → Q × W.lvl 0} {B : P × W.lvl 0 → W.lvl 0}
    (hC : IsPartialQuadrant (ScBanach.const P) Ct) (hf : IsBasicGerm Ct 𝒮.G f B) :
    ∃ r > 0, ∀ x ∈ (𝒮.toShiftedBasicData hC.isQuadrantLike hf).G₀.U 0,
      (𝒮.toShiftedBasicData hC.isQuadrantLike hf).g x = 0 → ‖x‖ < r →
        x.1 ∈ (𝒮.toShiftedBasicData hC.isQuadrantLike hf).𝒞.N 0 ∩ (Ct ×ˢ Set.univ) ∧
          x.2 = 𝒮.XB.toBase 1 ((𝒮.toShiftedBasicData hC.isQuadrantLike hf).δ x.1) := by
  set 𝒟 := 𝒮.toShiftedBasicData hC.isQuadrantLike hf with h𝒟
  obtain ⟨r₁, hr₁, hreg⟩ := hA 𝒮 hC hf (𝒟.basic.contraction.rad' 0)
    (𝒟.basic.contraction.rad'_pos 0)
  have hprad := 𝒟.basic.contraction.prad_pos 0
  refine ⟨min r₁ (𝒟.basic.contraction.prad 0), lt_min hr₁ hprad, fun x hxU hx0 hxr => ?_⟩
  obtain ⟨a, w⟩ := x
  obtain ⟨w₁, hw₁, hw₁r⟩ := hreg (a, w) hxU hx0 (hxr.trans_le (min_le_left _ _))
  have ha_norm : ‖a‖ < 𝒟.basic.contraction.prad 0 :=
    lt_of_le_of_lt (norm_fst_le (a, w)) (hxr.trans_le (min_le_right _ _))
  have haCt : a ∈ Ct ×ˢ (Set.univ : Set 𝒮.Cs) := by
    have := 𝒟.G₀.U_subset 0 hxU
    rw [ScBanach.paramProd_lvlSet] at this
    exact this.1
  have haN : a ∈ 𝒟.𝒞.N 0 ∩ (Ct ×ˢ Set.univ) := by
    refine ⟨?_, haCt⟩
    show a ∈ Metric.ball 0 (𝒟.basic.contraction.prad 0)
    rw [Metric.mem_ball, dist_zero_right]; exact ha_norm
  have hwO : w₁ ∈ 𝒟.𝒞.O 0 := by
    show w₁ ∈ Metric.ball 0 (𝒟.basic.contraction.rad' 0)
    rw [Metric.mem_ball, dist_zero_right]; exact hw₁r
  have hmem1 := 𝒟.𝒞.mem_G 0 a haN w₁ hwO
  have hmem1' : ((a, w₁) : (ScBanach.paramProd (P × 𝒮.Cs) 𝒮.XB) 1) ∈ 𝒟.G₀.U 1 := by
    rw [← 𝒟.G₁_U 0]; exact hmem1
  have hg₁ : 𝒟.g₁ (a, w₁) = 0 := by
    rw [𝒟.g₁_eq _ hmem1']
    apply (ScBanach.paramProd (Q × 𝒮.Zs) 𝒮.XB).toBase_injective 1
    rw [(𝒟.isScSmooth 0).toBase_levelMap hmem1', ScBanach.paramProd_toBase, map_zero]
    change 𝒟.g (a, 𝒮.XB.toBase 1 w₁) = 0
    rw [hw₁]; exact hx0
  have hwδ : w₁ = 𝒟.δ a := 𝒟.eq_δ haN hwO hmem1 (by rw [hg₁]; rfl)
  exact ⟨haN, by rw [← hw₁, hwδ]⟩

#rt_check RoundTrip.V3_37.zeros_eq_δ_of_A [Polyfold.StabilityData.lemma_3_42]

end RoundTrip.V3_37
