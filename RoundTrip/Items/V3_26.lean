import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_26

/-!
Round trip for V3_26 (Theorem 3.29).  `A` is the conjunction of the types of the theorems cited by
the comparison: `Polyfold.theorem_3_3_2`, `Polyfold.theorem_3_3_2_of_isSc0ContractionGerm`,
`Polyfold.ContractionGerm.incl_fixLvl`, `Polyfold.ContractionGerm.eq_sol` and
`Polyfold.exists_fixedPoint_continuousOn` (none has universe parameters: `P : Type`, `Λ X : Type`).
`ContractionGerm.sol` is a definition (vocabulary).

`A → B`:
* existence: `theorem_3_3_2_of_isSc0ContractionGerm` (in `A`) for B's sc⁰-contraction germ, the
  partial quadrant being quadrant-like;
* uniqueness as a germ: the same conjunct of `A` gives a canonical solution germ `δ₀` on `V₀` and a
  radius `r` with uniqueness of solutions `‖w‖ < r` over `V₀`; two solution germs `δ`, `δ'` of `B`
  are continuous with `δ(0) = δ'(0) = 0`, so both agree with `δ₀` on
  `V'' = V ∩ V' ∩ V₀ ∩ {‖δ‖ < r} ∩ {‖δ'‖ < r}`.
-/

namespace RoundTrip.V3_26
open Polyfold

/-- The project's statement: Theorem 3.29 and the lemmas cited with it. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_3_2 ∧ type_of% @Polyfold.theorem_3_3_2_of_isSc0ContractionGerm ∧
    type_of% @Polyfold.ContractionGerm.incl_fixLvl ∧ type_of% @Polyfold.ContractionGerm.eq_sol ∧
    type_of% @Polyfold.exists_fixedPoint_continuousOn

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_3_2, @Polyfold.theorem_3_3_2_of_isSc0ContractionGerm,
    @Polyfold.ContractionGerm.incl_fixLvl, @Polyfold.ContractionGerm.eq_sol,
    @Polyfold.exists_fixedPoint_continuousOn⟩

section Glue

variable {n : ℕ} {W : ScBanach} {Ct : Set (Fin n → ℝ)}

/-- A solution germ is continuous on level `0`, and `{‖δ‖ < r}` is relatively open there. -/
lemma exists_open_ball_preimage {V : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct}
    {δ : (Fin n → ℝ) → W.lvl 0} (hδ : IsSc0Germ V δ) (hδ0 : δ 0 = 0) {r : ℝ} (hr : 0 < r) :
    ∃ u : Set (Fin n → ℝ), IsOpen u ∧ (0 : Fin n → ℝ) ∈ u ∧
      ∀ a ∈ u ∩ V.U 0, ‖δ a‖ < r := by
  have hcont : ContinuousOn δ (V.U 0) :=
    (hδ.continuousOn 0).congr fun a _ => (levelMap_zero δ a).symm
  obtain ⟨u, hu, hueq⟩ := (continuousOn_iff'.1 hcont) (Metric.ball (0 : W.lvl 0) r)
    Metric.isOpen_ball
  have h0 : (0 : Fin n → ℝ) ∈ δ ⁻¹' Metric.ball (0 : W.lvl 0) r ∩ V.U 0 :=
    ⟨by rw [Set.mem_preimage, hδ0]; exact Metric.mem_ball_self hr, V.zero_mem 0⟩
  rw [hueq] at h0
  refine ⟨u, hu, h0.1, fun a ha => ?_⟩
  rw [← hueq] at ha
  have := ha.1
  rwa [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at this

end Glue

theorem A_to_B : A → B := by
  intro hA n W Ct G Bm hPQ h
  have hC : IsQuadrantLike (ScBanach.const (Fin n → ℝ)) Ct := hPQ.isQuadrantLike
  obtain ⟨V₀, δ₀, hδ₀, hδ₀0, hmem₀, hsol₀, r, hr, huniq⟩ := hA.2.1 hC h
  refine ⟨⟨V₀, δ₀, hδ₀, hδ₀0, fun a ha => ⟨?_, hsol₀ a ha⟩⟩, ?_⟩
  · have := hmem₀ 0 a ha
    rwa [levelMap_zero] at this
  · intro V V' δ δ' hs hs'
    obtain ⟨u, hu, hu0, hur⟩ := exists_open_ball_preimage hs.1 hs.2.1 hr
    obtain ⟨u', hu', hu'0, hu'r⟩ := exists_open_ball_preimage hs'.1 hs'.2.1 hr
    let V'' : ScNbhdGerm (ScBanach.const (Fin n → ℝ)) Ct :=
      { U := fun m => V.U m ∩ V'.U m ∩ V₀.U m ∩ (u ∩ u')
        nested := fun m x hx =>
          ⟨⟨⟨V.nested m x hx.1.1.1, V'.nested m x hx.1.1.2⟩, V₀.nested m x hx.1.2⟩, hx.2⟩
        zero_mem := fun m => ⟨⟨⟨V.zero_mem m, V'.zero_mem m⟩, V₀.zero_mem m⟩, hu0, hu'0⟩
        relOpen := fun m => by
          obtain ⟨T, hT, hVm⟩ := V.relOpen m
          obtain ⟨T', hT', hV'm⟩ := V'.relOpen m
          obtain ⟨T₀, hT₀, hV₀m⟩ := V₀.relOpen m
          refine ⟨T ∩ T' ∩ T₀ ∩ (u ∩ u'), ((hT.inter hT').inter hT₀).inter (hu.inter hu'), ?_⟩
          rw [hVm, hV'm, hV₀m]
          ext a
          simp only [Set.mem_inter_iff]
          tauto }
    refine ⟨V'', fun m a ha => ha.1.1, fun a ha => ?_⟩
    have haV : a ∈ V.U 0 := ha.1.1.1
    have haV' : a ∈ V'.U 0 := ha.1.1.2
    have haV₀ : a ∈ V₀.U 0 := ha.1.2
    have h1 : δ a = δ₀ a :=
      huniq a haV₀ (δ a) (hur a ⟨ha.2.1, haV⟩) (hs.2.2 a haV).2
    have h2 : δ' a = δ₀ a :=
      huniq a haV₀ (δ' a) (hu'r a ⟨ha.2.2, haV'⟩) (hs'.2.2 a haV').2
    rw [h1, h2]

#rt_check RoundTrip.V3_26.A_to_B [Polyfold.theorem_3_3_2,
  Polyfold.theorem_3_3_2_of_isSc0ContractionGerm, Polyfold.ContractionGerm.incl_fixLvl,
  Polyfold.ContractionGerm.eq_sol, Polyfold.exists_fixedPoint_continuousOn]

end RoundTrip.V3_26
