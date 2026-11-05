import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_60

open Set Filter Topology Function Module
open scoped ContDiff NNReal

noncomputable section

namespace RoundTrip.V3_60
open Polyfold

/-- The project's statement: `InvData.half_norm_le`, `InvData.norm_sub_le`, `InvData.injOn`,
`InvData.ball_inter_subset_image`, `InvData.image_relOpen` (no universe parameters; `V : Type`). -/
def A : Prop :=
  type_of% @Polyfold.InvData.half_norm_le ∧ type_of% @Polyfold.InvData.norm_sub_le ∧
    type_of% @Polyfold.InvData.injOn ∧ type_of% @Polyfold.InvData.ball_inter_subset_image ∧
    type_of% @Polyfold.InvData.image_relOpen

theorem A_holds : A :=
  ⟨@Polyfold.InvData.half_norm_le, @Polyfold.InvData.norm_sub_le, @Polyfold.InvData.injOn,
    @Polyfold.InvData.ball_inter_subset_image, @Polyfold.InvData.image_relOpen⟩

/-- B's hypotheses give the project's `InvData` with `j = 1` (hypothesis (3) is used only through
`d_C = 0 ⟺ interior`, `degIndex_eq_zero_iff`). -/
lemma invData_of_hyp {Rn : Type} [NormedAddCommGroup Rn] [NormedSpace ℝ Rn]
    [FiniteDimensional ℝ Rn] {C U : Set Rn} {f : Rn → Rn} (h : Hyp373 Rn C U f) :
    InvData C U f 1 := by
  obtain ⟨hC, hUrel, hconv, -, hf, hmaps, -, hDf, hdeg⟩ := h
  have hUC : U ⊆ C := by obtain ⟨O, -, rfl⟩ := hUrel; exact inter_subset_right
  refine ⟨hC, hUrel, hconv, hmaps, le_rfl, contDiffOn_infty.1 hf 1, fun x hx => hDf x hx,
    fun x hx => ?_⟩
  rw [← degIndex_eq_zero_iff hC (hUC hx), ← degIndex_eq_zero_iff hC (hmaps hx), hdeg x hx]

/-- A ⇒ B: `image_relOpen` gives `f(U)` relatively open; `half_norm_le`, `norm_sub_le` give the
estimate; openness of `f : U → f(U)`: the left inverse `g = invFunOn f U` is `2`-Lipschitz on
`f(U)` by `half_norm_le` (and `f` injective on `U` by the same estimate), and
`f(O ∩ U) = g⁻¹(O) ∩ f(U)`. -/
theorem A_to_B : A → B := by
  rintro ⟨hhalf, hle, -, -, hrel⟩
  intro Rn _ _ _ C U f hyp
  classical
  have h := invData_of_hyp hyp
  have hinj : InjOn f U := by
    intro x hx x' hx' hxx'
    have := hhalf h hx hx'
    rw [hxx', sub_self, norm_zero] at this
    have h2 : ‖x' - x‖ ≤ 0 := by linarith
    exact (sub_eq_zero.1 (norm_le_zero_iff.1 h2)).symm
  set g : Rn → Rn := Function.invFunOn f U with hgdef
  have hgU : ∀ y ∈ f '' U, g y ∈ U := fun y hy => Function.invFunOn_mem hy
  have hfg : ∀ y ∈ f '' U, f (g y) = y := fun y hy => Function.invFunOn_eq hy
  have hgf : ∀ x ∈ U, g (f x) = x := fun x hx => hinj.leftInvOn_invFunOn hx
  have hgc : ContinuousOn g (f '' U) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := (2 : ℝ≥0)) fun y hy y' hy' => ?_).continuousOn
    rw [dist_eq_norm, dist_eq_norm]
    have := hhalf h (hgU y' hy') (hgU y hy)
    rw [hfg y hy, hfg y' hy'] at this
    push_cast
    linarith
  refine ⟨hrel h, fun S hSU hS => ?_, fun x hx x' hx' => ⟨?_, ?_⟩⟩
  · obtain ⟨O, hO, rfl⟩ := hS
    obtain ⟨u, hu, hueq⟩ := continuousOn_iff'.1 hgc O hO
    refine ⟨u, hu, ?_⟩
    rw [← hueq]
    ext y
    constructor
    · rintro ⟨x, ⟨hxO, hxU⟩, rfl⟩
      exact ⟨by rw [mem_preimage, hgf x hxU]; exact hxO, x, hxU, rfl⟩
    · rintro ⟨hyO, hy⟩
      exact ⟨g y, ⟨hyO, hgU y hy⟩, hfg y hy⟩
  · exact hhalf h hx' hx
  · exact hle h hx' hx

#rt_check RoundTrip.V3_60.A_to_B [Polyfold.InvData.half_norm_le, Polyfold.InvData.norm_sub_le,
  Polyfold.InvData.injOn, Polyfold.InvData.ball_inter_subset_image,
  Polyfold.InvData.image_relOpen]

end RoundTrip.V3_60
