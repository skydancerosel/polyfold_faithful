import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V6_40

/-! Round trip for V6_40 (formula (94) and the continuity of the stabilized orientations).

A (universes at `0`) is the conjunction of the theorems `coord_stabIota`, `continuousOn_stabD`,
`stabD_ne_zero`, `isLineOrientation_stabRay` (WITH the sign `stabSign T = (−1)^{dim coker T}`,
the rays `α(T_q) Φ(o(T_q))` form an orientation) and `not_isLineOrientation_stabRay_uncorrected`
(WITHOUT the sign they need not, an instance over `Q = ℝ`).

B (the blind reading, the text taken literally) is the uncorrected statement for every family over
`J = [0, 1]`: the rays `Φ(o(T_q))` of `λ(ker(T_q ⊕ φ_q))` always form an orientation.  B is false:
`not_B` below transports the project's `StabCounterexample` (`T_q = f(q) · 1` on `ℝ`,
`f(q) = q/(1 + |q|)`, `φ = pr₀`) to `J` along `t ↦ t₀` (the jump of `dim coker T` is at the end
point `t = 0`) and repeats its sign argument in the frame `(1, −f(q))`.  It uses only the
counterexample's lemmas (`stabRays_eq`, `coord_x0`, `coord_xNe`, `stab_x0`, `stab_xNe`, `D₂_eq`,
`continuousWithinAt_section_iff`), not the item's theorems (checked by `#rt_check`).
-/

namespace RoundTrip.V6_40
open Polyfold Set Filter Topology

/-- The project's statement, universes instantiated at `0`. -/
def A : Prop :=
  type_of% @Polyfold.coord_stabIota.{0, 0} ∧
  type_of% @Polyfold.continuousOn_stabD.{0, 0, 0} ∧
  type_of% @Polyfold.stabD_ne_zero.{0, 0} ∧
  type_of% @Polyfold.isLineOrientation_stabRay.{0, 0, 0} ∧
  type_of% @Polyfold.not_isLineOrientation_stabRay_uncorrected

theorem A_holds : A :=
  ⟨@Polyfold.coord_stabIota.{0, 0}, @Polyfold.continuousOn_stabD.{0, 0, 0},
    @Polyfold.stabD_ne_zero.{0, 0}, @Polyfold.isLineOrientation_stabRay.{0, 0, 0},
    @Polyfold.not_isLineOrientation_stabRay_uncorrected⟩

/-! ### `¬ B`: the counterexample, moved to `J = [0, 1]` -/

/-- `t ↦ t₀ : J → ℝ`. -/
def g : C(J, ℝ) := ⟨fun t => (t : Fin 1 → ℝ) 0, (continuous_apply 0).comp continuous_subtype_val⟩

/-- The family `T_t = f(t₀) · 1` over `J`. -/
noncomputable def Tj (t : J) : ℝ →L[ℝ] ℝ := StabCounterexample.T (g t)

/-- `sign_of_ray` for a single vector. -/
theorem sign_of_ray' {b c : ℝ} {v : StabCounterexample.Λ.det b}
    (hc : c • StabCounterexample.ε.wedgeAt b ≠ 0) (h : v ≠ 0)
    (heq : rayOfNeZero ℝ v h = rayOfNeZero ℝ (c • StabCounterexample.ε.wedgeAt b) hc) :
    0 < c * StabCounterexample.ε.coord b v := by
  have hsr := ((ray_eq_iff _ _).1 heq).map (StabCounterexample.ε.coord b)
  rw [LinearMap.map_smul, StabCounterexample.ε.coord_wedgeAt (mem_univ b), smul_eq_mul,
    mul_one] at hsr
  have hc0 : c ≠ 0 := fun h0 => hc (by rw [h0, zero_smul])
  have hl0 : StabCounterexample.ε.coord b v ≠ 0 := fun h0 =>
    h (by rw [← StabCounterexample.ε.coord_smul_wedgeAt (mem_univ b) v, h0, zero_smul])
  rw [mul_comm]
  exact (sameRay_real_iff hl0 hc0).1 hsr

/-- A continuous map `ℝ → J` through `iccZero` with `t₀ > 0` for `x > 0`. -/
noncomputable def ι (x : ℝ) : J :=
  ⟨pt1 (projIcc (0 : ℝ) 1 zero_le_one x), pt1_mem_Icc (projIcc (0 : ℝ) 1 zero_le_one x).2⟩

theorem continuous_ι : Continuous ι :=
  ((continuous_pi fun _ => continuous_subtype_val.comp continuous_projIcc)).subtype_mk _

theorem ι_zero : ι 0 = iccZero := by
  refine Subtype.ext ?_
  change pt1 (projIcc (0 : ℝ) 1 zero_le_one 0 : ℝ) = pt1 0
  rw [projIcc_left]

theorem g_ι_pos {x : ℝ} (hx : 0 < x) : 0 < g (ι x) := by
  change 0 < (projIcc (0 : ℝ) 1 zero_le_one x : ℝ)
  rw [coe_projIcc]
  exact lt_max_of_lt_right (lt_min one_pos hx)

/-- **B is false.** -/
theorem not_B : ¬ B := by
  intro hB
  have hTF : ∀ t, (Tj t).IsFredholm := fun t =>
    StabCounterexample.hC _ (StabCounterexample.T_mem (g t))
  have hs : ∀ t : J, Function.Surjective ((Tj t).coprod StabCounterexample.φ) := fun t =>
    StabCounterexample.hφ (g t)
  have hΛ : ∀ t, (StabCounterexample.Λ.comp g).L t =
      LinearMap.ker ((Tj t).coprod StabCounterexample.φ).toLinearMap := fun t => rfl
  -- the orientation of `DET` along `t ↦ T_t`: the chart section `S ↦ (γ^0_S)⁻¹ ω(S)`
  let o : ∀ t, Module.Ray ℝ (fredholmDet (Tj t)) := fun t =>
    StabCounterexample.o ⟨Tj t, StabCounterexample.T_mem (g t)⟩
  have ho : IsContAlong Tj hTF o := by
    intro q₀
    refine ⟨univ, univ_mem, fun t => StabCounterexample.chart0.coordInv ⟨Tj t, hTF t⟩ 1, ?_,
      fun t _ => ⟨StabCounterexample.coordInv_one_ne_zero
        (S := ⟨Tj t, hTF t⟩) (StabCounterexample.T_mem (g t)), rfl⟩⟩
    have hc : Continuous fun t : J => (⟨Tj t, hTF t⟩ : FredholmOp ℝ ℝ) :=
      (StabCounterexample.continuous_T.comp g.continuous).subtype_mk _
    exact (StabCounterexample.continuousOn_coordInv_one.comp_continuous hc
      fun t => StabCounterexample.T_mem (g t)).continuousOn
  have hor := hB ℝ ℝ 1 Tj hTF (fun _ => StabCounterexample.φ) hs
    (StabCounterexample.continuous_T.comp g.continuous) continuous_const
    (StabCounterexample.Λ.comp g) hΛ o ho
  -- the rays are those of the counterexample, at `g t`
  change IsLineOrientation (StabCounterexample.Λ.comp g).det
    (fun t => StabCounterexample.stabRays (g t)) at hor
  obtain ⟨U, hU, σ, hσc, hσ⟩ := hor iccZero
  set K : ℝ := (StabCounterexample.D₁ * (StabCounterexample.D₂ 1)⁻¹)⁻¹ with hK
  -- the sign at `t = 0` (`dim coker T_0 = 1`)
  have hpos0 : 0 < K * StabCounterexample.ε.coord 0 (σ iccZero) := by
    obtain ⟨h0, hr0⟩ := StabCounterexample.stabRays_eq StabCounterexample.x0 one_ne_zero
      StabCounterexample.stab_x0
    obtain ⟨hσ0, hσr⟩ := hσ iccZero (mem_of_mem_nhds hU)
    have := sign_of_ray' (v := σ iccZero) h0 hσ0 (hσr.symm.trans hr0)
    rwa [StabCounterexample.coord_x0, mul_one] at this
  -- the sign at `t` with `t₀ ≠ 0` (`dim coker T_t = 0`)
  have hneg : ∀ t ∈ U, g t ≠ 0 → K * StabCounterexample.ε.coord (g t) (σ t) < 0 := by
    intro t ht ht0
    obtain ⟨h1, hr1⟩ := StabCounterexample.stabRays_eq (StabCounterexample.xNe ht0)
      (inv_ne_zero (neg_ne_zero.2 (StabCounterexample.f_ne_zero ht0)))
      (StabCounterexample.stab_xNe ht0)
    obtain ⟨hσ1, hσr⟩ := hσ t ht
    have := sign_of_ray' (v := σ t) h1 hσ1 (hσr.symm.trans hr1)
    rw [StabCounterexample.coord_xNe, StabCounterexample.D₂_eq] at this
    have hc : (StabCounterexample.D₁ * (StabCounterexample.f (g t) *
        StabCounterexample.D₂ 1)⁻¹)⁻¹ * (-StabCounterexample.f (g t))⁻¹ = -K := by
      have h := StabCounterexample.f_ne_zero ht0
      rw [hK]
      by_cases hD₁ : StabCounterexample.D₁ = 0
      · simp [hD₁]
      by_cases hD₂ : StabCounterexample.D₂ 1 = 0
      · simp [hD₂]
      field_simp
    rw [hc, neg_mul] at this
    linarith
  -- continuity at `iccZero`, in the pulled-back frame
  have hcont : ContinuousAt (fun t => K * StabCounterexample.ε.coord (g t) (σ t)) iccZero :=
    ((((StabCounterexample.Λ.comp g).continuousWithinAt_section_iff
      (StabCounterexample.ε.comp g) (mem_univ (g iccZero))).1
        (hσc iccZero (mem_of_mem_nhds hU))).continuousAt hU).const_mul K
  have hev : ∀ᶠ t in 𝓝 iccZero, t ∈ U ∧ 0 < K * StabCounterexample.ε.coord (g t) (σ t) :=
    (Filter.eventually_of_mem hU fun _ h => h).and (hcont.eventually (lt_mem_nhds hpos0))
  have hev' : ∀ᶠ x in 𝓝 (0 : ℝ), ι x ∈ U ∧
      0 < K * StabCounterexample.ε.coord (g (ι x)) (σ (ι x)) := by
    have ht : Tendsto ι (𝓝 0) (𝓝 iccZero) := by
      rw [← ι_zero]; exact continuous_ι.tendsto 0
    exact ht.eventually hev
  obtain ⟨x, ⟨hxU, hx⟩, hx0⟩ :=
    ((hev'.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  exact lt_asymm hx (hneg (ι x) hxU (g_ι_pos hx0).ne')

/-- `A ⇒ B` fails: A holds and B does not. -/
theorem not_A_to_B : ¬ (A → B) := fun h => not_B (h A_holds)

/-- `B ⇒ A`, only ex falso (B is false). -/
theorem B_to_A : B → A := fun h => absurd h not_B

#rt_check RoundTrip.V6_40.B_to_A [Polyfold.coord_stabIota, Polyfold.continuousOn_stabD,
  Polyfold.stabD_ne_zero, Polyfold.isLineOrientation_stabRay,
  Polyfold.not_isLineOrientation_stabRay_uncorrected]
#rt_check RoundTrip.V6_40.not_B [Polyfold.coord_stabIota, Polyfold.continuousOn_stabD,
  Polyfold.stabD_ne_zero, Polyfold.isLineOrientation_stabRay,
  Polyfold.not_isLineOrientation_stabRay_uncorrected]
#rt_overlap RoundTrip.V6_40.B_to_A [Polyfold.coord_stabIota, Polyfold.continuousOn_stabD,
  Polyfold.stabD_ne_zero, Polyfold.isLineOrientation_stabRay,
  Polyfold.not_isLineOrientation_stabRay_uncorrected]

end RoundTrip.V6_40
