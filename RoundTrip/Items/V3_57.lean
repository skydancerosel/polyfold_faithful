import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_57

open Set Filter Topology Function Module

noncomputable section

namespace RoundTrip.V3_57
open Polyfold

/-- The project's statement: `lemma_3_8_13` (the model `ℝⁿ ⊕ W`, no universe parameters),
`lemma_3_8_13_core`, `exists_rayDecomp` and `exists_lipschitz_small` (an arbitrary normed space;
universe instantiated at `0`). -/
def A : Prop :=
  type_of% @Polyfold.lemma_3_8_13 ∧ type_of% @Polyfold.lemma_3_8_13_core.{0} ∧
    type_of% @Polyfold.exists_rayDecomp.{0} ∧ type_of% @Polyfold.exists_lipschitz_small.{0}

theorem A_holds : A :=
  ⟨@Polyfold.lemma_3_8_13, @Polyfold.lemma_3_8_13_core.{0}, @Polyfold.exists_rayDecomp.{0},
    @Polyfold.exists_lipschitz_small.{0}⟩

/-- A ⇒ B, through the conjunct `lemma_3_8_13`: B's `τ : N → E₁` is pushed to `E₀` by `ι₁` and set
to `0` off the cone, so that it is `Y`-valued everywhere (as `lemma_3_8_13` demands); B's good
complement (sc-splitting) gives the project's algebraic one. -/
theorem A_to_B : A → B := by
  rintro ⟨h70, -, -, -⟩
  intro n W N _ _ hint Y hY τ hτY hτ hτ0 hDτ
  classical
  obtain ⟨hsplit, ε, hε, hgood⟩ := hY
  have hNY : IsCompl N Y := by simpa using hsplit.2.2 0
  have hYg : IsGoodComplement _ (quadrant n W 0) N Y := ⟨hNY, ε, hε, hgood⟩
  have hN : IsInGoodPosition _ (quadrant n W 0) N := ⟨hint, Y, hYg⟩
  set D : Set N := Subtype.val ⁻¹' quadC n W with hD
  have hDq : (Subtype.val ⁻¹' quadrant n W 0 : Set N) = D := rfl
  have hDconv : Convex ℝ D := (quadrant_convex n W 0).linear_preimage N.subtype
  have hUD : UniqueDiffOn ℝ D := uniqueDiffOn_convex hDconv hint
  have h0D : (0 : N) ∈ D := fun i => le_refl _
  -- `τ' = ι₁ ∘ τ` on the cone, `0` off it
  set τ' : N → (Emod n W).lvl 0 :=
    fun v => if (v : (Emod n W).lvl 0) ∈ quadC n W then (Emod n W).toBase 1 (τ v) else 0
    with hτ'def
  have hτ'D : ∀ v ∈ D, τ' v = (Emod n W).toBase 1 (τ v) := fun v hv => by
    simp only [hτ'def]; exact if_pos (show (v : (Emod n W).lvl 0) ∈ quadC n W from hv)
  have hτ'Y : ∀ v, τ' v ∈ Y := fun v => by
    by_cases hv : (v : (Emod n W).lvl 0) ∈ quadC n W
    · rw [hτ'D v hv]; exact hτY v hv
    · simp only [hτ'def]; rw [if_neg hv]; exact Y.zero_mem
  have hτ'C : ContDiffOn ℝ 1 τ' D :=
    ((Emod n W).toBase 1).contDiff.comp_contDiffOn hτ |>.congr fun v hv => hτ'D v hv
  have hτ'0 : τ' 0 = 0 := by rw [hτ'D 0 h0D, hτ0, map_zero]
  have hDτ'0 : fderivWithin ℝ τ' D 0 = 0 := by
    have h1 := ((Emod n W).toBase 1).hasFDerivAt.comp_hasFDerivWithinAt (0 : N) hDτ
    rw [ContinuousLinearMap.comp_zero] at h1
    have h2 : HasFDerivWithinAt τ' (0 : N →L[ℝ] (Emod n W).lvl 0) D 0 :=
      h1.congr (fun v hv => hτ'D v hv) (hτ'D 0 h0D)
    exact h2.fderivWithin (hUD 0 h0D)
  obtain ⟨ρ, hρ, hmain⟩ := h70 hN hYg τ' hτ'Y (by rw [hDq]; exact hτ'C) hτ'0
    (by rw [hDq]; exact hDτ'0)
  refine ⟨ρ, hρ, fun v hv hvW hvρ => ?_⟩
  obtain ⟨hmem, hdeg⟩ := hmain v hv hvρ
  have hv1 : (v : (Fin n → ℝ) × W.lvl 0).1 ≠ 0 := fun h => hvW fun i => congrFun h i
  have h := hdeg hv1
  rw [hτ'D v hv] at h hmem
  rw [← hDq, h, degIndex_quadrant hmem]
  rfl

#rt_check RoundTrip.V3_57.A_to_B [Polyfold.lemma_3_8_13, Polyfold.lemma_3_8_13_core,
  Polyfold.exists_rayDecomp, Polyfold.exists_lipschitz_small]

end RoundTrip.V3_57
