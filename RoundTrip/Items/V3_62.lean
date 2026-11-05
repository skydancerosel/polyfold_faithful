import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_62

/-! Round trip for V3_62 (Lemma 3.77: the inverse is `C¹`).

`A` is the conjunction of the types of `Polyfold.InvData.hasFDerivWithinAt_inv` and
`Polyfold.InvData.contDiffOn_inverse_deriv` (no universe parameters: `V : Type`).

Neither direction is proved; the two statements have different hypothesis sets.

* `A → B`: `A` is stated under `InvData` (Proposition 3.73's hypotheses: `U` convex,
  `‖Df(x) − 1‖ ≤ 1/2` on `U`, interior points preserved), whereas `B` (Lemma 3.77 as quoted)
  assumes only that `f : U → f(U)` is a homeomorphism onto a relatively open set with every `Df(x)`
  invertible.  An `f` satisfying `B`'s hypotheses need not satisfy `InvData` on any neighbourhood
  (normalizing `Df(x₀)` to `1` by composing with `Df(x₀)⁻¹` does not preserve `C`), so `A` does not
  apply.  `A_to_B373` proves `B` from `A` on `B`'s hypotheses plus the three extra `InvData`
  conditions.
* `B → A`: `A` is stated for `C^j` maps (`j ≥ 1`), `B` only for `C^∞` maps; and
  `contDiffOn_inverse_deriv` (`x ↦ [Df(x)]⁻¹` is `C^{j−1}` on `U`) is a statement about `f` alone
  that `B` (whose conclusion is about `g`) does not contain.  `B_to_A_smooth` proves the first
  conjunct of `A` from `B` for `C^∞` maps. -/

open Set Filter Topology Function Module
open scoped ContDiff NNReal

noncomputable section

namespace RoundTrip.V3_62
open Polyfold

/-- The project's statement (no universe parameters; `V : Type`). -/
def A : Prop :=
  (type_of% @Polyfold.InvData.hasFDerivWithinAt_inv) ∧
    (type_of% @Polyfold.InvData.contDiffOn_inverse_deriv)

theorem A_holds : A :=
  ⟨@Polyfold.InvData.hasFDerivWithinAt_inv, @Polyfold.InvData.contDiffOn_inverse_deriv⟩

lemma ringInverse_cle {Rn : Type} [NormedAddCommGroup Rn] [NormedSpace ℝ Rn] (e : Rn ≃L[ℝ] Rn) :
    Ring.inverse (e : Rn →L[ℝ] Rn) = (e.symm : Rn →L[ℝ] Rn) := by
  rw [ContinuousLinearMap.ringInverse_equiv, ContinuousLinearMap.inverse_equiv]

/-- The homeomorphism `U ≃ₜ f(U)` from continuity of `f`, `g` and the inverse identities. -/
def homeoOf {Rn : Type} [TopologicalSpace Rn] {U : Set Rn} {f g : Rn → Rn}
    (hf : ContinuousOn f U) (hg : ContinuousOn g (f '' U)) (hgU : ∀ y ∈ f '' U, g y ∈ U)
    (hgf : ∀ x ∈ U, g (f x) = x) (hfg : ∀ y ∈ f '' U, f (g y) = y) : U ≃ₜ (f '' U) where
  toFun x := ⟨f x, mem_image_of_mem f x.2⟩
  invFun y := ⟨g y, hgU y y.2⟩
  left_inv x := Subtype.ext (hgf x x.2)
  right_inv y := Subtype.ext (hfg y y.2)
  continuous_toFun := (continuousOn_iff_continuous_domRestrict.1 hf).subtype_mk _
  continuous_invFun := (continuousOn_iff_continuous_domRestrict.1 hg).subtype_mk _

/-! ### `A → B` on Proposition 3.73's hypothesis set (diagnostic) -/

/-- `B` with the three extra hypotheses of `InvData`: `U` convex, `‖Df(x) − 1‖ ≤ 1/2`, and
`x ∈ int C ⟺ f(x) ∈ int C` on `U`. -/
def B373 : Prop :=
  ∀ (Rn : Type) [NormedAddCommGroup Rn] [NormedSpace ℝ Rn] [FiniteDimensional ℝ Rn]
    (C U : Set Rn) (f : Rn → Rn),
    IsPartialQuadrant (ScBanach.const Rn) C →
    IsRelOpen C U → Convex ℝ U →
    ContDiffOn ℝ ∞ f U → Set.MapsTo f U C →
    (∀ x ∈ U, ‖fderivWithin ℝ f U x - 1‖ ≤ 1 / 2) →
    (∀ x ∈ U, x ∈ interior C ↔ f x ∈ interior C) →
    IsRelOpen C (f '' U) →
    (∃ h : U ≃ₜ (f '' U), ∀ x : U, (h x : Rn) = f x) →
    (∀ x ∈ U, ∃ e : Rn ≃L[ℝ] Rn, (e : Rn →L[ℝ] Rn) = fderivWithin ℝ f U x) →
    ∀ g : Rn → Rn, (∀ y ∈ f '' U, g y ∈ U ∧ f (g y) = y) →
      ContDiffOn ℝ 1 g (f '' U) ∧
      ∀ y ∈ f '' U, ∀ e : Rn ≃L[ℝ] Rn, (e : Rn →L[ℝ] Rn) = fderivWithin ℝ f U (g y) →
        HasFDerivWithinAt g (e.symm : Rn →L[ℝ] Rn) (f '' U) y

theorem A_to_B373 : A → B373 := by
  intro hA Rn _ _ _ C U f hC hU hconv hf hmaps hDf hint _ _ _ g hg
  have h : InvData C U f 1 := ⟨hC, hU, hconv, hmaps, le_rfl, contDiffOn_infty.1 hf 1, hDf, hint⟩
  have hgeq : ∀ y ∈ f '' U, g y = InvData.inv U f y := fun y hy =>
    h.injOn (hg y hy).1 (h.inv_mem hy) (by rw [(hg y hy).2, h.apply_inv hy])
  have hderiv : ∀ y ∈ f '' U,
      HasFDerivWithinAt g (Ring.inverse (fderivWithin ℝ f U (g y))) (f '' U) y := by
    intro y hy
    have := hA.1 h hy
    rw [← hgeq y hy] at this
    exact this.congr (fun y' hy' => hgeq y' hy') (hgeq y hy)
  have hgc : ContinuousOn g (f '' U) :=
    h.continuousOn_inv.congr fun y hy => hgeq y hy
  refine ⟨?_, fun y hy e he => ?_⟩
  · rw [show (1 : WithTop ℕ∞) = 0 + 1 from (zero_add 1).symm]
    refine (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn h.uniqueDiffOn_image).2
      ⟨fun hω => absurd hω (by simp), fun y => Ring.inverse (fderivWithin ℝ f U (g y)), ?_,
        hderiv⟩
    exact contDiffOn_zero.2 ((hA.2 h).continuousOn.comp hgc fun y hy => (hg y hy).1)
  · rw [← ringInverse_cle e, he]
    exact hderiv y hy

#rt_check RoundTrip.V3_62.A_to_B373
  [Polyfold.InvData.hasFDerivWithinAt_inv, Polyfold.InvData.contDiffOn_inverse_deriv]

/-! ### `B → A` for `C^∞` maps, first conjunct (diagnostic) -/

/-- The first conjunct of `A` (`hasFDerivWithinAt_inv`) for `C^∞` maps. -/
def AinvSmooth : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (C U : Set V) (f : V → V) (j : ℕ), InvData C U f j → ContDiffOn ℝ ∞ f U →
    ∀ y ∈ f '' U, HasFDerivWithinAt (InvData.inv U f)
      (Ring.inverse (fderivWithin ℝ f U (InvData.inv U f y))) (f '' U) y

theorem B_to_A_smooth : B → AinvSmooth := by
  intro hB V _ _ _ C U f j h hf y hy
  let hhom := homeoOf h.continuousOn h.continuousOn_inv (fun y hy => h.inv_mem hy)
    (fun x hx => h.inv_apply hx) (fun y hy => h.apply_inv hy)
  have key := hB V C U f h.isPartialQuadrant h.relOpen hf h.mapsTo h.image_relOpen
    ⟨hhom, fun x => rfl⟩
    (fun x hx => ⟨ContinuousLinearEquiv.unitsEquiv ℝ V (h.derivUnit hx), by
      ext v; rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.unitsEquiv_apply,
        h.derivUnit_val hx]⟩)
    (InvData.inv U f) (fun y hy => ⟨h.inv_mem hy, h.apply_inv hy⟩)
  have hx := h.inv_mem hy
  set e := ContinuousLinearEquiv.unitsEquiv ℝ V (h.derivUnit hx) with he
  have he' : (e : V →L[ℝ] V) = fderivWithin ℝ f U (InvData.inv U f y) := by
    ext v; rw [ContinuousLinearEquiv.coe_coe, he, ContinuousLinearEquiv.unitsEquiv_apply,
      h.derivUnit_val hx]
  rw [← he', ringInverse_cle]
  exact key.2 y hy e he'

#rt_check RoundTrip.V3_62.B_to_A_smooth
  [Polyfold.InvData.hasFDerivWithinAt_inv, Polyfold.InvData.contDiffOn_inverse_deriv]

end RoundTrip.V3_62

end
