import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_36

/-!
Round trip for V3_36 (Corollary 3.41).  `A` is the conjunction of the types of
`Polyfold.StabilityData.corollary_3_41`, `Polyfold.StabilityData.exists_isFredholm_Dfs'`,
`Polyfold.StabilityData.exists_ker_Dfs'_inf_eq_bot`, `Polyfold.isFredholm_add_of_norm_lt`,
`Polyfold.HasFiniteIndex.surjective_of_finrank_ker_le` and
`Polyfold.StabilityData.Kop_isCompactOperator` (no universe parameters).

Glue for `A → B` (only the conjunct `corollary_3_41` is needed):
* B's sc⁺-germ `s` has values in `(ℝᴺ ⊕ W)¹`; the project's `StabilityData` carries only the
  `W`-component `s₂ : → W¹`.  The `ℝᴺ`-component is absorbed into the basic germ:
  `h' = h + (s₁, 0)` is again basic (same `W`-component, same `B`), and `h + s = h' + (0, s₂)`.
* The splitting data of `StabilityData` exists by Proposition 1.10
  (`StabilityData.exists_of_scPlus`).
* B's arbitrary derivative family `D` of `f` agrees with the project's `Dfs'` on `U₁`
  (uniqueness of derivatives on the quadrant, `IsSc1Germ.scDerivGerm_eqOn`).
* A's "every zero `x ∈ U` with `|x|₀ < r`" gives B's relatively open `U' = U₀ ∩ B_r(0)`.
* Mathlib's `IsFredholm` gives B's `IsFredholmOp`, and `fredholmIndex` is B's `fredIdx`.
-/

namespace RoundTrip.V3_36
open Polyfold

/-- The project's statement: Corollary 3.41 and the lemmas of its proof. -/
def A : Prop :=
  type_of% @Polyfold.StabilityData.corollary_3_41 ∧
  type_of% @Polyfold.StabilityData.exists_isFredholm_Dfs' ∧
  type_of% @Polyfold.StabilityData.exists_ker_Dfs'_inf_eq_bot ∧
  type_of% @Polyfold.isFredholm_add_of_norm_lt ∧
  type_of% @Polyfold.HasFiniteIndex.surjective_of_finrank_ker_le ∧
  type_of% @Polyfold.StabilityData.Kop_isCompactOperator

theorem A_holds : A :=
  ⟨@Polyfold.StabilityData.corollary_3_41, @Polyfold.StabilityData.exists_isFredholm_Dfs',
    @Polyfold.StabilityData.exists_ker_Dfs'_inf_eq_bot, @Polyfold.isFredholm_add_of_norm_lt,
    @Polyfold.HasFiniteIndex.surjective_of_finrank_ker_le,
    @Polyfold.StabilityData.Kop_isCompactOperator⟩

section Glue

variable (Q : Type) [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] (W : ScBanach)

/-- `(Q ⊕ W)¹ → W¹`, `(q, w) ↦ w`. -/
noncomputable def sndShiftOp : ScOperator (ScBanach.paramProd Q W).shift W.shift where
  lvl m := ContinuousLinearMap.snd ℝ Q (W (m + 1))
  incl_comm _ _ := rfl

/-- `(Q ⊕ W)¹ → Q ⊕ W`, `(q, w) ↦ (q, 0)`. -/
noncomputable def fstShiftOp : ScOperator (ScBanach.paramProd Q W).shift (ScBanach.paramProd Q W) where
  lvl m := (ContinuousLinearMap.inl ℝ Q (W m)).comp (ContinuousLinearMap.fst ℝ Q (W (m + 1)))
  incl_comm m x := by
    change ((x.1, W.incl m 0) : Q × W m) = (x.1, 0)
    rw [map_zero]

end Glue

theorem A_to_B : A → B := by
  intro hA n N W Ct G h Bh s hPQ hb hs hs0 f D hD hsurj
  have hCq : IsQuadrantLike (ScBanach.paramProd (Fin n → ℝ) W) (Ct ×ˢ Set.univ) :=
    hPQ.isQuadrantLike.paramProd W
  -- the `W`-component of `s`, and `h' = h + (s₁, 0)`
  obtain ⟨s₂, hs₂⟩ : ∃ s₂ : (Fin n → ℝ) × W 0 → W 1,
      s₂ = (sndShiftOp (Fin N → ℝ) W) 0 ∘ s := ⟨_, rfl⟩
  have hs₂apply : ∀ x, s₂ x = (s x).2 := fun x => by rw [hs₂]; rfl
  have hs₂sm : IsScSmoothGerm (E := ScBanach.paramProd (Fin n → ℝ) W) (F := W.shift) G s₂ := by
    rw [hs₂]; exact fun k => (hs k).operator_comp hCq (sndShiftOp (Fin N → ℝ) W)
  obtain ⟨h', hh'⟩ : ∃ h' : (Fin n → ℝ) × W 0 → (Fin N → ℝ) × W 0,
      h' = (ScBanach.paramProd (Fin N → ℝ) W).addOp 0 ∘
        pairMap (E := ScBanach.paramProd (Fin n → ℝ) W) (F := ScBanach.paramProd (Fin N → ℝ) W)
          (G := ScBanach.paramProd (Fin N → ℝ) W) h ((fstShiftOp (Fin N → ℝ) W) 0 ∘ s) := ⟨_, rfl⟩
  have hh'apply : ∀ x, h' x = h x + ((s x).1, (0 : W 0)) := fun x => by rw [hh']; rfl
  have hh'sm : IsScSmoothGerm (E := ScBanach.paramProd (Fin n → ℝ) W)
      (F := ScBanach.paramProd (Fin N → ℝ) W) G h' := by
    rw [hh']
    exact fun k => ((hb.isScSmooth k).pair hCq
      ((hs k).operator_comp hCq (fstShiftOp (Fin N → ℝ) W))).operator_comp hCq _
  have hs00 : (s 0).1 = 0 := by rw [hs0]; rfl
  have hb' : IsBasicGerm Ct G h' Bh := by
    refine ⟨hh'sm, ?_, fun x hx => ?_, hb.contraction⟩
    · rw [hh'apply, hb.f_zero, hs00, Prod.mk_zero_zero, add_zero]
    · rw [hh'apply, Prod.snd_add, add_zero]; exact hb.snd_eq x hx
  obtain ⟨𝒮, h𝒮G, h𝒮s⟩ := StabilityData.exists_of_scPlus (Ct := Ct) hs₂sm
    (by rw [hs₂apply, hs0]; rfl)
  subst h𝒮G
  have hfeq : 𝒮.fsum h' = f := by
    funext x
    rw [StabilityData.fsum_apply, h𝒮s, hh'apply, hs₂apply]
    change _ = h x + (ScBanach.paramProd (Fin N → ℝ) W).toBase 1 (s x)
    rw [ScBanach.paramProd_toBase]
    refine Prod.ext ?_ ?_
    · simp
    · simp only [Prod.snd_add, add_zero]
  have hD' : IsSc1GermWith (F := ScBanach.paramProd (Fin N → ℝ) W) 𝒮.G (𝒮.fsum h') D := by
    rw [hfeq]; exact hD
  have hDeq : Set.EqOn (𝒮.Dfs' h') D (𝒮.G.U 1) := IsSc1Germ.scDerivGerm_eqOn hCq hD'
  have hsurjA : Function.Surjective (𝒮.Dfs h') := by
    have : 𝒮.Dfs h' = D 0 := hDeq (𝒮.G.zero_mem 1)
    rw [this]; exact hsurj
  obtain ⟨r, hr, H⟩ := hA.1 𝒮 hPQ hb' hsurjA
  obtain ⟨O, hO, hU⟩ := 𝒮.G.relOpen 0
  refine ⟨𝒮.G.U 0 ∩ Metric.ball 0 r, ⟨O ∩ Metric.ball 0 r, hO.inter Metric.isOpen_ball, ?_⟩,
    ⟨𝒮.G.zero_mem 0, Metric.mem_ball_self hr⟩, Set.inter_subset_left, fun x hx hfx => ?_⟩
  · rw [hU, ScBanach.paramProd_lvlSet]
    ext y
    simp only [Set.mem_inter_iff]
    tauto
  have hxr : ‖x‖ < r := by
    have := hx.2; rwa [Metric.mem_ball, dist_zero_right] at this
  obtain ⟨x₁, hx₁, hx₁U, hF, hI, hS⟩ := H x hx.1 hxr (by rw [hfeq]; exact hfx)
  have e := hDeq hx₁U
  refine ⟨x₁, hx₁U, hx₁, ?_, ?_, ?_⟩
  · rw [← e]; exact hS
  · rw [← e]
    exact ⟨hF.finite_ker, hF.isClosed_range, (Polyfold.IsFredholm.hasFiniteIndex hF).finite_coker⟩
  · rw [← e]
    change fredholmIndex (𝒮.Dfs' h' x₁) = _
    rw [hI, Module.finrank_fin_fun, Module.finrank_fin_fun]

#rt_check RoundTrip.V3_36.A_to_B [Polyfold.StabilityData.corollary_3_41,
  Polyfold.StabilityData.exists_isFredholm_Dfs', Polyfold.StabilityData.exists_ker_Dfs'_inf_eq_bot,
  Polyfold.isFredholm_add_of_norm_lt, Polyfold.HasFiniteIndex.surjective_of_finrank_ker_le,
  Polyfold.StabilityData.Kop_isCompactOperator]

end RoundTrip.V3_36
