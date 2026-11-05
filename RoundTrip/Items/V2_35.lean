import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_35

/-! Round trip for V2_35 (Proposition 2.30: `Tf(x) T^R_xO = T^R_yO'`, `Tf(x) C_xO = C_yO'`).

`A` is the conjunction of the types of the theorems listed for the item (no universe parameters):
`IsScSmoothRetractMap.isDiffeoGerm`, `ScRetraction.IsDiffeoGerm.deriv_inv_deriv`,
`ScRetraction.IsDiffeoGerm.deriv_deriv_inv`, `proposition_2_30_reduced`, `proposition_2_30_cone`.
`ScRetraction.IsDiffeoGerm` (a germ `F : r(U) → r'(U')` with inverse `G`, `F ∘ r`, `G ∘ r'` sc¹)
is vocabulary.

* `A → B`: B's germ (`f` sc-smooth from `O ∩ V` to `O' ∩ V'` with sc-smooth inverse `g`) is an
  `IsDiffeoGerm` between `RV` (onto `O ∩ V`) and `R'.restrict V'` (onto `O' ∩ V'`) by A's
  `isDiffeoGerm`; A's `proposition_2_30_*` at `x₁` give the two equalities with the reduced
  spaces / partial cones computed with `RV` and `R'.restrict V'`.  These equal the ones computed
  with `R` and `R'` (B's): the tangent space at a point of `O ∩ V` is the same for every
  retraction onto `O ∩ V` (Proposition 2.4) and for a retraction onto `O` (restriction,
  `scDeriv_restrict`).  `levelMap (f ∘ RV) 1 x₁ = y₁` by injectivity of `E'₁ → E'₀`.
* `B → A` fails for a genuine difference in generality: A's Proposition 2.30 is for germs with
  `F ∘ r`, `G ∘ r'` only sc¹ and at every level-1 point `x ∈ O₁`; B only for sc-smooth germs at
  smooth points `x ∈ O_∞` (the text's hypotheses).  B cannot give A's sc¹ / level-1 case without
  re-proving the proposition (sign argument and density).  A's three auxiliary lemmas
  (`isDiffeoGerm`, the chain-rule identities `deriv_inv_deriv`, `deriv_deriv_inv`) are not in B
  either. -/

namespace RoundTrip.V2_35
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.IsScSmoothRetractMap.isDiffeoGerm) ∧
  (type_of% @Polyfold.ScRetraction.IsDiffeoGerm.deriv_inv_deriv) ∧
  (type_of% @Polyfold.ScRetraction.IsDiffeoGerm.deriv_deriv_inv) ∧
  (type_of% @Polyfold.proposition_2_30_reduced) ∧
  (type_of% @Polyfold.proposition_2_30_cone)

theorem A_holds : A :=
  ⟨@Polyfold.IsScSmoothRetractMap.isDiffeoGerm, @Polyfold.ScRetraction.IsDiffeoGerm.deriv_inv_deriv,
    @Polyfold.ScRetraction.IsDiffeoGerm.deriv_deriv_inv, @Polyfold.proposition_2_30_reduced,
    @Polyfold.proposition_2_30_cone⟩

/-- The tangent space at a level-1 point of `O ∩ V` is the same for a retraction `RV` onto `O ∩ V`
and a retraction `R` onto `O` (Proposition 2.4 and restriction). -/
lemma range_scDeriv_eq {E : ScBanach} {C O V : Set (E.lvl 0)} (hV : IsOpen V)
    (R : ScRetraction E C) (hR : R.retract = O) (RV : ScRetraction E C) (hRV : RV.retract = O ∩ V)
    {x₁ : E.lvl 1} (hx : x₁ ∈ E.lvlSet (O ∩ V) 1) :
    range (scDeriv RV.U RV x₁) = range (scDeriv R.U R x₁) := by
  set RR := R.restrict hV
  have hRR : RR.retract = O ∩ V := by rw [R.restrict_retract, hR]
  have hxV : x₁ ∈ E.lvlSet RV.retract 1 := by rw [hRV]; exact hx
  have hxR : x₁ ∈ E.lvlSet RR.retract 1 := by rw [hRR]; exact hx
  have h1 : range (scDeriv RV.U RV x₁) = range (scDeriv RR.U RR x₁) := by
    ext v
    rw [← RV.mem_tangent_iff_mem_range hxV, ← RR.mem_tangent_iff_mem_range hxR,
      proposition_2_4 RV RR (by rw [hRV, hRR])]
  rw [h1, R.scDeriv_restrict hV (RR.lvlSet_retract_subset 1 hxR)]

/-- `A → B`. -/
theorem A_to_B : A → B := by
  rintro ⟨hgerm, -, -, hred, hcone⟩
  intro E C O _ E' C' O' _ x hxO _ f g V V' hfg x₁ hx₁ y₁ hy₁ R hR R' hR' RV hRV n W T hT
    n' W' T' hT'
  obtain ⟨hV, hV', hxV, -, hf, hg, hgf, hfg'⟩ := hfg
  set R₁ := R'.restrict hV'
  have hR₁ : R₁.retract = O' ∩ V' := by rw [R'.restrict_retract, hR']
  have germ : RV.IsDiffeoGerm R₁ f g :=
    hgerm (by rw [hRV, hR₁]; exact hf) (by rw [hRV, hR₁]; exact hg) (by rw [hRV]; exact hgf)
      (by rw [hR₁]; exact hfg')
  have hxOV : x₁ ∈ E.lvlSet (O ∩ V) 1 := by
    change E.toBase 1 x₁ ∈ O ∩ V
    rw [hx₁]; exact ⟨hxO, hxV⟩
  have hxRV : x₁ ∈ E.lvlSet RV.retract 1 := by rw [hRV]; exact hxOV
  have hy : levelMap (f ∘ RV) 1 x₁ = y₁ := by
    apply E'.toBase_injective 1
    rw [germ.toBase_image hxRV, hx₁, hy₁]
  have hyR₁ : y₁ ∈ E'.lvlSet R₁.retract 1 := by
    rw [hR₁]
    change E'.toBase 1 y₁ ∈ O' ∩ V'
    rw [hy₁]; exact hf.mapsTo ⟨hxO, hxV⟩
  have hyU : y₁ ∈ E'.lvlSet (R'.restrict hV').U 1 := R₁.lvlSet_retract_subset 1 hyR₁
  have hrange := range_scDeriv_eq hV R hR RV hRV hxOV
  have hrange' : range (scDeriv R₁.U R₁ y₁) = range (scDeriv R'.U R' y₁) := by
    rw [R'.scDeriv_restrict hV' hyU]
  constructor
  · have h := hred germ hxRV T hT T' hT'
    rw [hy] at h
    have e1 : reducedTangentSpaceWith RV T x₁ = reducedTangentSpaceWith R T x₁ := by
      apply SetLike.coe_injective
      simp only [reducedTangentSpaceWith, Submodule.coe_inf, LinearMap.coe_range,
        ContinuousLinearMap.coe_coe]
      rw [hrange]
    have e2 : reducedTangentSpaceWith R₁ T' y₁ = reducedTangentSpaceWith R' T' y₁ :=
      reducedTangentSpaceWith_restrict R' hV' T' hyU
    rw [← e1, ← e2, ← h, Submodule.map_coe]
    rfl
  · have h := hcone germ hxRV T hT T' hT'
    rw [hy] at h
    have e1 : partialConeWith RV T x₁ = partialConeWith R T x₁ := by
      simp only [partialConeWith]; rw [hrange]
    have e2 : partialConeWith R₁ T' y₁ = partialConeWith R' T' y₁ := by
      simp only [partialConeWith]; rw [hrange']
    rw [← e1, ← e2, ← h]

#rt_check RoundTrip.V2_35.A_to_B [Polyfold.IsScSmoothRetractMap.isDiffeoGerm, Polyfold.ScRetraction.IsDiffeoGerm.deriv_inv_deriv, Polyfold.ScRetraction.IsDiffeoGerm.deriv_deriv_inv, Polyfold.proposition_2_30_reduced, Polyfold.proposition_2_30_cone]

end RoundTrip.V2_35
