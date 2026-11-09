import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_38

/-! Round trip for V2_38 (Corollary 2.32: `d_{X_C} = d_C`).

`A` is the conjunction of the types of `Polyfold.corollary_2_4_13`,
`IsRelOpenInQuadrant.degIndex_le`, `IsRelOpenInQuadrant.degIndex_le_degIndex_of_lvl1` and
`degIndexWith_le_of_germ` (no universe parameters).

Same notions on both sides: B's `X_C` is the project's `hC.toMPolyfold hne` for the relatively
open subset `U = C` of `C`, `d_X` is `MPolyfold.degIndex`, `d_C` is `degIndex E C`.

`A → B`: `C` is relatively open in itself (`relOpen_self`, `V = E₀`), and `corollary_2_4_13` at
`U = C`.

`B → A` fails for a genuine reason: A's fourth conjunct `degIndexWith_le_of_germ` (the core of
Theorem 2.31) is a statement about germs `F : (U₀, x) → (O', F x)` from a relatively open
`U₀ ⊆ C` onto a RETRACT `O'`, with `F` and `G ∘ r'` only sc¹: `d_C(x) ≤ d_{C'}(F x)` at level-1
points.  B is about the M-polyfold index `d_X`, defined through sc-SMOOTH charts, of partial
quadrants only; an sc¹ germ is not a chart, so B says nothing about it (with sc-smooth `F`, `G`
it would follow from B, `F` being a chart of `X_{U₀}`).  The other three conjuncts do follow from
B (`B_to_cor`, rt_check OK): A states the corollary for every nonempty relatively open `U ⊆ C`,
and `X_U` is sc-diffeomorphic to the open subset `{c | c ∈ U}` of `X_C` (`incl_isScDiffeoOn`, new
glue), so Proposition 2.24 (`proposition_2_4_4`, a non-item lemma) reduces it to B at `U = C`;
`degIndex_le` and `degIndex_le_degIndex_of_lvl1` are the two inequalities of that equality. -/

namespace RoundTrip.V2_38
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.corollary_2_4_13) ∧ (type_of% @Polyfold.IsRelOpenInQuadrant.degIndex_le) ∧
    (type_of% @Polyfold.IsRelOpenInQuadrant.degIndex_le_degIndex_of_lvl1) ∧
    (type_of% @Polyfold.degIndexWith_le_of_germ)

theorem A_holds : A :=
  ⟨@Polyfold.corollary_2_4_13, @Polyfold.IsRelOpenInQuadrant.degIndex_le,
    @Polyfold.IsRelOpenInQuadrant.degIndex_le_degIndex_of_lvl1, @Polyfold.degIndexWith_le_of_germ⟩

/-- A partial quadrant is relatively open in itself. -/
theorem relOpen_self {E : ScBanach} {C : Set (E 0)} (hC : IsPartialQuadrant E C) :
    IsRelOpenInQuadrant E C C :=
  ⟨hC, ⟨univ, isOpen_univ, (univ_inter C).symm⟩⟩

theorem A_to_B : A → B := by
  intro hA E C hC
  exact ⟨relOpen_self hC, fun hne x => hA.1 (relOpen_self hC) hne x⟩

/-! ### Glue: `X_U` is an open piece of `X_C` -/

section Glue

variable {E : ScBanach} {C U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U) (hne : U.Nonempty)

include hU in
lemma U_subset_C : U ⊆ C := by
  obtain ⟨O, _, hO⟩ := hU.relOpen
  rw [hO]; exact inter_subset_right

/-- The inclusion `U → C`. -/
def incl : U → C := fun u => ⟨u.1, U_subset_C hU u.2⟩

open scoped Classical in
/-- A left inverse `C → U` of the inclusion. -/
noncomputable def back : C → U := fun c =>
  if h : (c : E 0) ∈ U then ⟨c, h⟩ else ⟨hne.some, hne.some_mem⟩

lemma back_val {c : C} (hc : (c : E 0) ∈ U) : ((back hne c : U) : E 0) = c := by
  unfold back; rw [dif_pos hc]

theorem incl_isScDiffeoOn (hC : IsRelOpenInQuadrant E C C) (hneC : C.Nonempty) :
    (hU.toMPolyfold hne).IsScDiffeoOn (hC.toMPolyfold hneC) (incl hU) (back hne)
      univ {c : C | (c : E 0) ∈ U} := by
  set SU : MChart U := (LocalModel.ofRelOpen hU).selfChart hne with hSUdef
  set SC : MChart C := (LocalModel.ofRelOpen hC).selfChart hneC with hSCdef
  have hSU : (hU.toMPolyfold hne).IsChart SU := hU.selfChart_isChart hne
  have hSC : (hC.toMPolyfold hneC).IsChart SC := hC.selfChart_isChart hneC
  obtain ⟨O, hO, hUO⟩ := hU.relOpen
  have hVopen : IsOpen {c : C | (c : E 0) ∈ U} := by
    have : {c : C | (c : E 0) ∈ U} = Subtype.val ⁻¹' O := by
      ext c
      change (c : E 0) ∈ U ↔ (c : E 0) ∈ O
      rw [hUO]
      exact ⟨fun h => h.1, fun h => ⟨h, c.2⟩⟩
    rw [this]; exact hO.preimage continuous_subtype_val
  refine ⟨?_, ?_, fun u _ => u.2, fun _ _ => mem_univ _, fun u _ => ?_, fun c hc => ?_⟩
  · have hcont : ContinuousOn (incl hU) univ :=
      (continuous_subtype_val.subtype_mk _).continuousOn
    refine MPolyfold.IsScSmoothOn.of_exists_charts isOpen_univ hcont fun x _ => ?_
    refine ⟨SU, SC, univ, hSU, hSC, isOpen_univ, mem_univ _,
      fun y _ => ⟨mem_univ _, mem_univ _⟩, fun _ _ => mem_univ _, ?_⟩
    have himg : SU '' univ = U := SU.image_source
    rw [himg]
    refine ((isScSmoothRetractMap_id (C := C) U).mono_target
      (fun z hz => U_subset_C hU hz)).congr fun z hz => ?_
    change z = ((incl hU (SU.symm z) : C) : E 0)
    have h1 : SU.symm z = ⟨z, hz⟩ := LocalModel.selfChart_symm_apply (LocalModel.ofRelOpen hU) hne hz
    rw [h1]
    rfl
  · have hcont : ContinuousOn (back hne) {c : C | (c : E 0) ∈ U} := by
      rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
      exact continuous_subtype_val.continuousOn.congr fun c hc => back_val hne hc
    refine MPolyfold.IsScSmoothOn.of_exists_charts hVopen hcont fun c hc => ?_
    refine ⟨SC, SU, {c : C | (c : E 0) ∈ U}, hSC, hSU, hVopen, hc,
      fun y hy => ⟨hy, mem_univ _⟩, fun _ _ => mem_univ _, ?_⟩
    have himg : SC '' {c : C | (c : E 0) ∈ U} = U := by
      ext z
      constructor
      · rintro ⟨c, hc, rfl⟩; exact hc
      · intro hz; exact ⟨⟨z, U_subset_C hU hz⟩, hz, rfl⟩
    rw [himg]
    refine (isScSmoothRetractMap_id (C := C) U).congr fun z hz => ?_
    change z = ((back hne (SC.symm z) : U) : E 0)
    have h1 : SC.symm z = ⟨z, U_subset_C hU hz⟩ :=
      LocalModel.selfChart_symm_apply (LocalModel.ofRelOpen hC) hneC (U_subset_C hU hz)
    rw [h1, back_val hne hz]
  · apply Subtype.ext
    exact back_val hne u.2
  · apply Subtype.ext
    exact back_val hne hc

end Glue

/-- From `B`: Corollary 2.32 for every nonempty relatively open `U ⊆ C` (A's first conjunct),
via Proposition 2.24 along `X_U ↪ X_C`. -/
theorem B_to_cor (hB : B) : type_of% @Polyfold.corollary_2_4_13 := by
  intro E C U hU hne x
  obtain ⟨hC, hBC⟩ := hB E C hU.isPartialQuadrant
  have hneC : C.Nonempty := ⟨x, U_subset_C hU x.2⟩
  rw [proposition_2_4_4 (incl_isScDiffeoOn hU hne hC hneC) (mem_univ x), hBC hneC]
  rfl

/-- From `B`: the first three conjuncts of `A`. -/
theorem B_to_A123 (hB : B) :
    (type_of% @Polyfold.corollary_2_4_13) ∧ (type_of% @Polyfold.IsRelOpenInQuadrant.degIndex_le) ∧
      (type_of% @Polyfold.IsRelOpenInQuadrant.degIndex_le_degIndex_of_lvl1) :=
  ⟨B_to_cor hB, fun hU hne x => le_of_eq (B_to_cor hB hU hne x),
    fun hU hne x _ => ge_of_eq (B_to_cor hB hU hne x)⟩

#rt_check RoundTrip.V2_38.A_to_B [Polyfold.corollary_2_4_13, Polyfold.IsRelOpenInQuadrant.degIndex_le,
  Polyfold.IsRelOpenInQuadrant.degIndex_le_degIndex_of_lvl1, Polyfold.degIndexWith_le_of_germ]
#rt_check RoundTrip.V2_38.B_to_A123 [Polyfold.corollary_2_4_13,
  Polyfold.IsRelOpenInQuadrant.degIndex_le,
  Polyfold.IsRelOpenInQuadrant.degIndex_le_degIndex_of_lvl1, Polyfold.degIndexWith_le_of_germ]
#rt_overlap RoundTrip.V2_38.B_to_A123 [Polyfold.corollary_2_4_13,
  Polyfold.IsRelOpenInQuadrant.degIndex_le,
  Polyfold.IsRelOpenInQuadrant.degIndex_le_degIndex_of_lvl1, Polyfold.degIndexWith_le_of_germ]

end RoundTrip.V2_38
