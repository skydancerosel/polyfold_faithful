import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_58

open Set Filter Topology Function Module
open scoped ContDiff

noncomputable section

namespace RoundTrip.V3_58
open Polyfold

/-- The project's statement: `theorem_3_8_15` (for `C^j`, `j ≥ 1`), `surjective_of_image_eq`,
`degIndex_map_eq`, `degIndex_eq_zero_iff` (no universe parameters; `V : Type`). -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_8_15 ∧ type_of% @Polyfold.surjective_of_image_eq ∧
    type_of% @Polyfold.degIndex_map_eq ∧ type_of% @Polyfold.degIndex_eq_zero_iff

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_8_15, @Polyfold.surjective_of_image_eq, @Polyfold.degIndex_map_eq,
    @Polyfold.degIndex_eq_zero_iff⟩

/-- A relatively open subset of a partial quadrant of a finite-dimensional space is a set of
unique differentiability. -/
lemma uniqueDiffOn_of_relOpen {Rn : Type} [NormedAddCommGroup Rn] [NormedSpace ℝ Rn]
    [FiniteDimensional ℝ Rn] {C U : Set Rn} (hC : IsPartialQuadrant (ScBanach.const Rn) C)
    (hU : ∃ O : Set Rn, IsOpen O ∧ U = O ∩ C) : UniqueDiffOn ℝ U := by
  obtain ⟨O, hO, rfl⟩ := hU
  have hCint : (interior C).Nonempty := by
    have := hC.interior_lvlSet_nonempty 0
    rwa [ScBanach.lvlSet_const] at this
  rw [inter_comm]
  exact (uniqueDiffOn_convex hC.convex hCint).inter hO

/-- **The `C¹` inverse of a `C^∞` map is `C^∞`** (bootstrapping `Dg = [Df ∘ g]⁻¹`): `f` smooth on
`U'`, `g : V' → U'` a `C¹` inverse of `f` (both sets of unique differentiability, `V' = f(U')`). -/
lemma contDiffOn_infty_inv {Rn : Type} [NormedAddCommGroup Rn] [NormedSpace ℝ Rn]
    [FiniteDimensional ℝ Rn] {U' V' : Set Rn} {f g : Rn → Rn} (hUD : UniqueDiffOn ℝ U')
    (hVD : UniqueDiffOn ℝ V') (hf : ContDiffOn ℝ ∞ f U') (hg : ContDiffOn ℝ (1 : ℕ) g V')
    (hmaps : MapsTo f U' V') (hgf : ∀ x ∈ U', g (f x) = x)
    (hfg : ∀ y ∈ V', f (g y) = y ∧ g y ∈ U') : ContDiffOn ℝ ∞ g V' := by
  have hf1 : ContDiffOn ℝ (1 : ℕ) f U' := contDiffOn_infty.1 hf 1
  -- `Df(x)` is a unit with inverse `Dg(f x)`
  have hunit : ∀ x ∈ U', ∃ u : (Rn →L[ℝ] Rn)ˣ, (u : Rn →L[ℝ] Rn) = fderivWithin ℝ f U' x ∧
      ((u⁻¹ : (Rn →L[ℝ] Rn)ˣ) : Rn →L[ℝ] Rn) = fderivWithin ℝ g V' (f x) := by
    intro x hx
    set y := f x with hydef
    have hy : y ∈ V' := hmaps hx
    have hgy : g y = x := hgf x hx
    have hfd : HasFDerivWithinAt f (fderivWithin ℝ f U' x) U' (g y) := by
      rw [hgy]; exact ((hf1.differentiableOn (by simp)) x hx).hasFDerivWithinAt
    have hgd : HasFDerivWithinAt g (fderivWithin ℝ g V' y) V' y :=
      ((hg.differentiableOn (by simp)) y hy).hasFDerivWithinAt
    have hcomp := hfd.comp y hgd (fun z hz => (hfg z hz).2)
    have hid : HasFDerivWithinAt (f ∘ g) (ContinuousLinearMap.id ℝ Rn) V' y :=
      (hasFDerivWithinAt_id y V').congr (fun z hz => (hfg z hz).1) (hfg y hy).1
    have heq := (hVD y hy).eq hcomp hid
    have h1 : fderivWithin ℝ f U' x * fderivWithin ℝ g V' y = 1 := heq
    have h1v : ∀ v, fderivWithin ℝ f U' x (fderivWithin ℝ g V' y v) = v := fun v =>
      congrArg (fun T : Rn →L[ℝ] Rn => T v) h1
    have hinjD : Injective (fderivWithin ℝ f U' x) :=
      (LinearMap.injective_iff_surjective (f := (fderivWithin ℝ f U' x : Rn →ₗ[ℝ] Rn))).2
        fun v => ⟨fderivWithin ℝ g V' y v, h1v v⟩
    have h2 : fderivWithin ℝ g V' y * fderivWithin ℝ f U' x = 1 := by
      ext v
      exact hinjD (h1v (fderivWithin ℝ f U' x v))
    exact ⟨⟨fderivWithin ℝ f U' x, fderivWithin ℝ g V' y, h1, h2⟩, rfl, rfl⟩
  have hDg : ∀ y ∈ V', fderivWithin ℝ g V' y = Ring.inverse (fderivWithin ℝ f U' (g y)) := by
    intro y hy
    obtain ⟨u, hu, hu'⟩ := hunit (g y) (hfg y hy).2
    rw [← hu, Ring.inverse_unit, hu', (hfg y hy).1]
  have key : ∀ k : ℕ, ContDiffOn ℝ k g V' := by
    intro k
    induction k with
    | zero => exact contDiffOn_zero.2 hg.continuousOn
    | succ k ih =>
      rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by push_cast; rfl]
      refine (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hVD).2
        ⟨fun hω => absurd hω (by simp), fun y => Ring.inverse (fderivWithin ℝ f U' (g y)), ?_,
          fun y hy => ?_⟩
      · have hD : ContDiffOn ℝ k (fderivWithin ℝ f U') U' :=
          (contDiffOn_infty.1 hf (k + 1)).fderivWithin hUD
            (by exact_mod_cast (show k + 1 ≤ k + 1 from le_rfl))
        have hΨ : ContDiffOn ℝ k (fun x => Ring.inverse (fderivWithin ℝ f U' x)) U' := by
          intro x hx
          obtain ⟨u, hu, -⟩ := hunit x hx
          have h2 : ContDiffAt ℝ k (Ring.inverse : (Rn →L[ℝ] Rn) → (Rn →L[ℝ] Rn))
              (u : Rn →L[ℝ] Rn) := contDiffAt_ringInverse ℝ u
          rw [hu] at h2
          exact h2.contDiffWithinAt.comp x (hD x hx) (mapsTo_univ _ _)
        exact hΨ.comp ih fun y hy => (hfg y hy).2
      · show HasFDerivWithinAt g (Ring.inverse (fderivWithin ℝ f U' (g y))) V' y
        rw [← hDg y hy]
        exact ((hg.differentiableOn (by simp)) y hy).hasFDerivWithinAt
  exact contDiffOn_infty.2 key

/-- A ⇒ B, from the conjunct `theorem_3_8_15` with `j = 1`; the `C¹` inverse is then `C^∞` by the
bootstrap `contDiffOn_infty_inv` (the project's theorem gives, for each `j`, possibly different
neighbourhoods, so the `C^∞` statement is not read off directly). -/
theorem A_to_B : A → B := by
  rintro ⟨h372, -, -, -⟩
  intro Rn _ _ _ C U f hC hUrel h0U hf hfC hf0 hDf hdeg
  obtain ⟨U', V', hU'rel, hV'rel, h0U', h0V', hU'U, himg, hinj, g, hg, hgf, hfg⟩ :=
    h372 (j := 1) ⟨hC, hUrel⟩ h0U le_rfl (contDiffOn_infty.1 hf 1) hfC hf0 hDf hdeg
  have hmaps : MapsTo f U' V' := fun x hx => himg ▸ mem_image_of_mem f hx
  have hfU' : ContDiffOn ℝ ∞ f U' := hf.mono hU'U
  refine ⟨U', V', g, hU'rel, hU'U, h0U', hV'rel, h0V', himg ▸ hinj.bijOn_image,
    fun y hy => ⟨(hfg y hy).2, (hfg y hy).1⟩, hfU', ?_⟩
  exact contDiffOn_infty_inv (uniqueDiffOn_of_relOpen hC hU'rel) (uniqueDiffOn_of_relOpen hC hV'rel)
    hfU' hg hmaps hgf fun y hy => hfg y hy

#rt_check RoundTrip.V3_58.A_to_B [Polyfold.theorem_3_8_15, Polyfold.surjective_of_image_eq,
  Polyfold.degIndex_map_eq, Polyfold.degIndex_eq_zero_iff]

end RoundTrip.V3_58
