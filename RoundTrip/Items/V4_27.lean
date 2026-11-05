import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_27

/-! Round trip for V4_27 (Theorem 4.2, (i) ⇒ (ii)).

`A` is the conjunction of the types of `Polyfold.MChart.IsCornerChart.mem_smooth`,
`Polyfold.MChart.IsCornerChart.exists_centred`, `Polyfold.MChart.IsCornerChart.exists_centred_tame`
(these three at universe `0`), `Polyfold.tangentSpace_relOpen` and `Polyfold.isInGoodPosition_top`.

`A → B`: from `HasCornerStructure`, every point lies in a corner chart (`hasCornerStructure_iff`);
`X₀ = X_∞` by `mem_smooth` (A) and `mem_smoothSet_iff`; `1₀¹` sc-smooth for every junk value by
`isScSmoothMap_toLevelOne_of_cover` (Proposition 4.8 in each corner chart, whose model is an
sc⁺-retract); the centred chart is `exists_centred` (A), tame with the identity retraction; for any
retraction `R` onto its model, `Dr(0)E = T₀O = E` (`tangentSpace_eq_range`, `tangentSpace_relOpen`
(A)), finite-dimensional, and in B's (sc-complement) good position with the sc-complement `0`
(`isInGoodPosition_top` (A) for the interior, `isScSplitting_bot_top`).

`B → A` is proved only VACUOUSLY (`B` unused): every conjunct of `A` is a local lemma about one
corner chart (or about a relatively open subset of a partial quadrant), stated for any chart of any
M-polyfold, not only for tame ones with a corner structure; B, a statement about the whole
M-polyfold, does not imply them.  They are short and are re-proved outright below (the project's
own arguments, avoiding the banned names). -/

namespace RoundTrip.V4_27
open Polyfold Set

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MChart.IsCornerChart.mem_smooth.{0}) ∧
    (type_of% @Polyfold.MChart.IsCornerChart.exists_centred.{0}) ∧
    (type_of% @Polyfold.MChart.IsCornerChart.exists_centred_tame.{0}) ∧
    (type_of% @Polyfold.tangentSpace_relOpen) ∧ (type_of% @Polyfold.isInGoodPosition_top)

theorem A_holds : A :=
  ⟨@Polyfold.MChart.IsCornerChart.mem_smooth.{0}, @Polyfold.MChart.IsCornerChart.exists_centred.{0},
    @Polyfold.MChart.IsCornerChart.exists_centred_tame.{0}, @Polyfold.tangentSpace_relOpen,
    @Polyfold.isInGoodPosition_top⟩

theorem A_to_B : A → B := by
  rintro ⟨hsmooth, hcentred, -, hrelOpen, htop⟩ X _ _ _ P _hT h
  have hloc := MPolyfold.hasCornerStructure_iff.1 h
  refine ⟨?_, fun x₀ => ?_, fun x => ?_⟩
  · -- `X₀ = X_∞`
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨χ, hχ, hx, hc⟩ := hloc x
    exact (MPolyfold.mem_smoothSet_iff hχ hx).2 (hsmooth hc (χ x))
  · -- `1₀¹` is sc-smooth
    exact (MPolyfold.isScSmoothMap_toLevelOne_of_cover x₀ fun x => by
      obtain ⟨χ, hχ, hx, hc⟩ := hloc x
      exact ⟨χ, hχ, hx, hc.isScPlusRetract⟩).2
  · -- the centred tame chart
    obtain ⟨χ, hχ, hx, hc⟩ := hloc x
    obtain ⟨ψ, hψ, hxψ, h0, hrel, hfin⟩ := hcentred hχ hc hx
    refine ⟨ψ, hψ, ⟨ScRetraction.id hrel, image_id _, ScRetraction.id_isTame _⟩, hxψ, h0,
      fun R hR => ?_⟩
    have h0O : (0 : ψ.model.E 0) ∈ ψ.model.O := h0 ▸ ψ.mapsTo_model x hxψ
    have h0R : (0 : ψ.model.E 1) ∈ ψ.model.E.lvlSet R.retract 1 := by
      rw [ScBanach.mem_lvlSet, map_zero, hR]; exact h0O
    have htan : tangentAtZero R = ⊤ := by
      have h1 := tangentSpace_eq_coe_submodule R h0R
      rw [hR, hrelOpen hrel (by rw [map_zero]; exact h0O)] at h1
      apply SetLike.coe_injective
      rw [Submodule.top_coe]
      exact h1.symm
    rw [htan]
    refine ⟨inferInstance, (htop ψ.model.isPartialQuadrant).interior_nonempty, ⊥,
      ψ.model.E.isScSplitting_bot_top.symm, 1, one_pos, fun n _ y hy _ => ?_⟩
    rw [(Submodule.mem_bot ℝ).1 hy, add_zero]

/-! ### `B → A`, vacuously: the conjuncts of `A` re-proved outright (B is not used) -/

theorem tangentSpace_relOpen' {E : ScBanach} {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U)
    {x : E 1} (hx : E.toBase 1 x ∈ U) : tangentSpace E C U x = univ := by
  have hret : (ScRetraction.id hU).retract = U := image_id U
  have hx' : x ∈ E.lvlSet (ScRetraction.id hU).retract 1 := by rw [hret]; exact hx
  have h := tangentSpace_eq_range (ScRetraction.id hU) hx'
  rw [hret] at h
  rw [h]
  have hD : scDeriv (ScRetraction.id hU).U (ScRetraction.id hU) x =
      ContinuousLinearMap.id ℝ (E 0) :=
    IsSc1.scDeriv_eqOn (isSc1With_id U) (hU.isScDomain.uniqueDiffWithinAt 1) hx
  rw [hD]
  exact range_id

theorem isInGoodPosition_top' {E : ScBanach} {C : Set (E 0)} (hC : IsPartialQuadrant E C) :
    IsInGoodPosition E C ⊤ where
  interior_nonempty := by
    obtain ⟨z, hz⟩ := hC.interior_lvlSet_nonempty 0
    have hopen : IsOpenMap (Subtype.val : (⊤ : Submodule ℝ (E 0)) → E 0) :=
      IsOpen.isOpenMap_subtype_val (s := ((⊤ : Submodule ℝ (E 0)) : Set (E 0)))
        (by rw [Submodule.top_coe]; exact isOpen_univ)
    refine ⟨⟨z, Submodule.mem_top⟩, ?_⟩
    rw [← hopen.preimage_interior_eq_interior_preimage continuous_subtype_val]
    exact hz
  exists_goodComplement := ⟨⊥, isCompl_top_bot, 1, one_pos, fun x _ p hp _ => by
    rw [(Submodule.mem_bot ℝ).1 hp, add_zero]⟩

theorem mem_smooth' {X : Type} [TopologicalSpace X] {χ : MChart X} (h : χ.IsCornerChart)
    (z : χ.model.E 0) : z ∈ χ.model.E.smooth := by
  have := h.finiteDimensional
  exact χ.model.E.mem_smooth_of_finiteDimensional z

theorem exists_centred' {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {P : MPolyfold X} {χ : MChart X} (hχ : P.IsChart χ) (hc : χ.IsCornerChart) {x : X}
    (hx : x ∈ χ.source) :
    ∃ ψ : MChart X, P.IsChart ψ ∧ x ∈ ψ.source ∧ ψ x = 0 ∧
      IsRelOpenInQuadrant ψ.model.E ψ.model.C ψ.model.O ∧ FiniteDimensional ℝ (ψ.model.E 0) := by
  obtain ⟨n, W, T, hT⟩ := χ.model.isPartialQuadrant
  have he : χ x ∈ χ.model.E.smooth := mem_smooth' hc (χ x)
  refine ⟨χ.recentre T hT (χ x) he, χ.recentre_isChart T hT (χ x) he hχ,
    χ.mem_recentre_source T hT (χ x) he hx rfl, χ.recentre_apply_self T hT (χ x) he rfl, ?_,
    hc.finiteDimensional⟩
  have hG := isOpen_recentreNbhd T (χ x)
  have h := relOpen_translate hT (hc.isRelOpenInQuadrant.inter_isOpen hG) inter_subset_right
  rw [← image_sub_const_eq_preimage_add'] at h
  rw [MChart.recentre_model_O]
  exact h

theorem exists_centred_tame' {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {P : MPolyfold X} {χ : MChart X} (hχ : P.IsChart χ) (hc : χ.IsCornerChart) {x : X}
    (hx : x ∈ χ.source) :
    ∃ ψ : MChart X, P.IsChart ψ ∧ x ∈ ψ.source ∧ ψ x = 0 ∧
      IsTameRetract ψ.model.E ψ.model.C ψ.model.O ∧
      ∃ N : Submodule ℝ (ψ.model.E 0), (N : Set (ψ.model.E 0)) =
        tangentSpace ψ.model.E ψ.model.C ψ.model.O 0 ∧ FiniteDimensional ℝ N ∧
        IsInGoodPosition ψ.model.E ψ.model.C N := by
  obtain ⟨ψ, hψ, hxψ, h0, hrel, hfin⟩ := exists_centred' hχ hc hx
  refine ⟨ψ, hψ, hxψ, h0, ⟨ScRetraction.id hrel, image_id _, ScRetraction.id_isTame _⟩, ⊤, ?_,
    inferInstance, isInGoodPosition_top' ψ.model.isPartialQuadrant⟩
  rw [Submodule.top_coe, tangentSpace_relOpen' hrel]
  rw [map_zero, ← h0]
  exact ψ.mapsTo_model x hxψ

/-- Vacuous: `A` holds outright (re-proved without the banned lemmas); `B` is not used. -/
theorem B_to_A : B → A := fun _ =>
  ⟨@mem_smooth', @exists_centred', @exists_centred_tame', @tangentSpace_relOpen',
    @isInGoodPosition_top'⟩

#rt_check RoundTrip.V4_27.A_to_B [Polyfold.MChart.IsCornerChart.mem_smooth,
  Polyfold.MChart.IsCornerChart.exists_centred, Polyfold.MChart.IsCornerChart.exists_centred_tame,
  Polyfold.tangentSpace_relOpen, Polyfold.isInGoodPosition_top]
#rt_check RoundTrip.V4_27.B_to_A [Polyfold.MChart.IsCornerChart.mem_smooth,
  Polyfold.MChart.IsCornerChart.exists_centred, Polyfold.MChart.IsCornerChart.exists_centred_tame,
  Polyfold.tangentSpace_relOpen, Polyfold.isInGoodPosition_top]
#rt_overlap RoundTrip.V4_27.B_to_A [Polyfold.MChart.IsCornerChart.mem_smooth,
  Polyfold.MChart.IsCornerChart.exists_centred, Polyfold.MChart.IsCornerChart.exists_centred_tame,
  Polyfold.tangentSpace_relOpen, Polyfold.isInGoodPosition_top]

end RoundTrip.V4_27
