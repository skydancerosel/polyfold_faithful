import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_49

/-! Round trip for V2_49 (Proposition 2.43: a face `F` of a tame retract `O` is the image of an
sc-smooth retraction `s : V* → V*`, a sub-M-polyfold of `O`, tame, with `d_F = d_O − 1`).

`A` is the conjunction of the types of the theorems among the item's declarations:
`proposition_2_5_15`, `killCoord_mem`, `killCoord_eq_self`, `LocalModel.isSubMPolyfold_of_isFace`,
`degIndexWith_eq_quadrantDeg_faceProj_add_one`, `proposition_2_5_15_tameModel`,
`MPolyfold.faceChart_compatible_subChart` (universe `0`) and `LocalModel.proposition_2_5_15_isTame`.
`killCoord`, `faceIncl`, `faceProj`, `MPolyfold.faceChart` are definitions (vocabulary).

`A → B`: B's retraction `s` is the `S` of `proposition_2_5_15` (`S.U ⊆ R.U`, `F ⊆ S.U`,
`S.retract = F`), after moving the face between `↥O` and `E₀` with `isFace_toMPolyfold_iff`
(item V2_46, not banned).  B's sub-M-polyfold data (`s|_V` sc-smooth on `V = O ∩ V*` in the
M-polyfold `O`, `V → V`, idempotent, image `F ∩ V`) is not a theorem of A: it is the body of the
proof of `isSubMPolyfold_of_isFace`, re-done here for any retraction `S` onto `F` (`subData_of`,
glue copied from the project's proof).  The tame/degree clause is `isSubMPolyfold_of_isFace` +
`proposition_2_5_15_isTame` (proof irrelevance for the sub-M-polyfold proof and the
paracompactness instance, supplied by `paracompactSpace_subtype`).

Harness: the statement of `proposition_2_5_15_isTame` contains the banned `isSubMPolyfold_of_isFace`
(the argument of `subPolyfold`), so every proof mentioning `A` reaches it hard.  As in V2_51/V2_53,
`A'` is `A` with that proof (and the instance) universally quantified; `A_to_A'` is a projection by
proof irrelevance and `A'_to_B` passes `#rt_check`; `A_to_B := A'_to_B ∘ A_to_A'`.

`B → A` fails genuinely: `proposition_2_5_15` asserts the specific retraction `S = r ∘ P_i`
(`P_i = killCoord T i`) on `S.U` and `F ⊆ f_i`; `proposition_2_5_15_tameModel` a tame model of `F`
through `faceProj`; `faceChart_compatible_subChart` a chart-compatibility lemma;
`degIndexWith_eq_quadrantDeg_faceProj_add_one` and the `killCoord` lemmas are coordinate facts.
B only asserts that SOME retraction onto `F` exists and the tame/degree conclusions.  B does give
`isSubMPolyfold_of_isFace` (`B_to_isSubMPolyfold`) and `proposition_2_5_15_isTame` for any
sub-M-polyfold proof (`B_to_isTame`), both `#rt_check` OK. -/

namespace RoundTrip.V2_49
open Polyfold Set

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.proposition_2_5_15) ∧ (type_of% @Polyfold.killCoord_mem) ∧
    (type_of% @Polyfold.killCoord_eq_self) ∧
    (type_of% @Polyfold.LocalModel.isSubMPolyfold_of_isFace) ∧
    (type_of% @Polyfold.degIndexWith_eq_quadrantDeg_faceProj_add_one) ∧
    (type_of% @Polyfold.proposition_2_5_15_tameModel) ∧
    (type_of% @Polyfold.MPolyfold.faceChart_compatible_subChart.{0}) ∧
    (type_of% @Polyfold.LocalModel.proposition_2_5_15_isTame)

theorem A_holds : A :=
  ⟨@Polyfold.proposition_2_5_15, @Polyfold.killCoord_mem, @Polyfold.killCoord_eq_self,
    @Polyfold.LocalModel.isSubMPolyfold_of_isFace,
    @Polyfold.degIndexWith_eq_quadrantDeg_faceProj_add_one, @Polyfold.proposition_2_5_15_tameModel,
    @Polyfold.MPolyfold.faceChart_compatible_subChart.{0},
    @Polyfold.LocalModel.proposition_2_5_15_isTame⟩

/-- `proposition_2_5_15_isTame` with the sub-M-polyfold proof and the paracompactness instance
quantified (they are propositions: equal to the project's by proof irrelevance). -/
def IsTame' : Prop :=
  ∀ (M : LocalModel) (hne : M.O.Nonempty) {n : ℕ} {W : ScBanach} (R : ScRetraction M.E M.C)
    (_ : R.retract = M.O) {T : ScIso M.E ((ScBanach.const (Fin n → ℝ)).prod W)}
    (_ : M.C = T 0 ⁻¹' quadrant n W 0) (_ : R.IsTameWith T) {F : Set M.O}
    (_ : (M.toMPolyfold hne).IsFace F) (hsub : (M.toMPolyfold hne).IsSubMPolyfold F)
    (_ : ParacompactSpace F),
    (MPolyfold.subPolyfold hsub).IsTame ∧
      ∀ x : F, (MPolyfold.subPolyfold hsub).degIndex x + 1 = (M.toMPolyfold hne).degIndex x.1

/-- `A` up to the proof term inside the statement of `proposition_2_5_15_isTame`. -/
def A' : Prop :=
  (type_of% @Polyfold.proposition_2_5_15) ∧ (type_of% @Polyfold.killCoord_mem) ∧
    (type_of% @Polyfold.killCoord_eq_self) ∧
    (type_of% @Polyfold.LocalModel.isSubMPolyfold_of_isFace) ∧
    (type_of% @Polyfold.degIndexWith_eq_quadrantDeg_faceProj_add_one) ∧
    (type_of% @Polyfold.proposition_2_5_15_tameModel) ∧
    (type_of% @Polyfold.MPolyfold.faceChart_compatible_subChart.{0}) ∧ IsTame'

theorem A_to_A' : A → A' := fun ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
  ⟨h1, h2, h3, h4, h5, h6, h7, fun M hne _ _ R hRM _ hT hR _ hF _ _ => h8 M hne R hRM hT hR hF⟩

/-! ### Glue: B's sub-M-polyfold data from any retraction onto the face -/

/-- The local model `(r(U), C, E)`. -/
abbrev Mod {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C) : LocalModel :=
  LocalModel.mk E C R.retract ⟨R, rfl⟩

/-- For any sc-smooth retraction `S` onto (the image in `E₀` of) `F ⊆ O`, `s|_V` with
`V = O ∩ S.U` is sc-smooth on `V` in the M-polyfold `O`, maps `V` to `V`, is idempotent there
and has image `F ∩ V` (the body of the project's proof of `isSubMPolyfold_of_isFace`). -/
theorem subData_of {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C)
    (hne : R.retract.Nonempty) {F : Set R.retract} (S : ScRetraction E C)
    (hSret : S.retract = Subtype.val '' F) :
    ((Mod R).toMPolyfold hne).IsScSmoothOn ((Mod R).toMPolyfold hne)
        (restrictB R.retract S.toFun) {y | y.1 ∈ S.U} ∧
      MapsTo (restrictB R.retract S.toFun) {y | y.1 ∈ S.U} {y | y.1 ∈ S.U} ∧
      (∀ y ∈ {y : R.retract | y.1 ∈ S.U},
        restrictB R.retract S.toFun (restrictB R.retract S.toFun y) =
          restrictB R.retract S.toFun y) ∧
      restrictB R.retract S.toFun '' {y | y.1 ∈ S.U} = F ∩ {y | y.1 ∈ S.U} := by
  classical
  have hRM : R.retract = (Mod R).O := rfl
  obtain ⟨W₀, hW₀, hSW⟩ := S.relOpen.relOpen
  have hOC : (Mod R).O ⊆ (Mod R).C := (Mod R).O_subset_C
  set V : Set R.retract := {y | y.1 ∈ S.U} with hV
  have hVo : IsOpen V := by
    have : V = Subtype.val ⁻¹' W₀ := by
      ext y; rw [hV, mem_ofPred_eq, mem_preimage, hSW]
      exact ⟨fun h => h.1, fun h => ⟨h, hOC y.2⟩⟩
    rw [this]; exact hW₀.preimage continuous_subtype_val
  have hSO : ∀ y ∈ V, S y ∈ R.retract := fun y hy => by
    have : S y ∈ S.retract := S.apply_mem_retract hy
    rw [hSret] at this
    obtain ⟨z, _, hz⟩ := this
    rw [← hz]; exact z.2
  set r := restrictB R.retract S.toFun with hrdef
  have hr : ∀ y ∈ V, (r y : E 0) = S y := fun y hy => by
    simp only [hrdef, restrictB, dif_pos (hSO y hy)]
  have hFG : ∀ y : R.retract, y ∈ F ↔ (y : E 0) ∈ Subtype.val '' F := fun y =>
    ⟨fun h => ⟨y, h, rfl⟩, fun ⟨z, hz, hzy⟩ => Subtype.val_injective hzy ▸ hz⟩
  refine ⟨?_, fun y hy => ?_, fun y hy => ?_, ?_⟩
  · -- sc-smoothness, in the chart `id` of `O`
    have hcont : ContinuousOn r V := by
      rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
      refine (S.isSc1.isSc0.continuousOn_base.comp continuous_subtype_val.continuousOn
        fun y hy => hy).congr fun y hy => hr y hy
    refine MPolyfold.IsScSmoothOn.of_exists_charts hVo hcont fun y hy => ?_
    refine ⟨(Mod R).selfChart hne, (Mod R).selfChart hne, V,
      ((Mod R).toMPolyfold hne).isChart_of_mem (mem_singleton _),
      ((Mod R).toMPolyfold hne).isChart_of_mem (mem_singleton _), hVo, hy,
      fun z hz => ⟨hz, mem_univ _⟩, fun _ _ => mem_univ _, ?_⟩
    have himV : ((Mod R).selfChart hne) '' V = R.retract ∩ W₀ := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨w.2, ?_⟩
        have : (w : E 0) ∈ S.U := hw
        rw [hSW] at this; exact this.1
      · rintro ⟨hzO, hzW⟩
        exact ⟨⟨z, hzO⟩, show z ∈ S.U by rw [hSW]; exact ⟨hzW, hOC hzO⟩, rfl⟩
    rw [himV]
    have hret : IsScRetract E C (R.retract ∩ W₀) := ⟨R.restrict hW₀, R.restrict_retract hW₀⟩
    have heq : ∀ z : E 0, z ∈ R.retract ∩ W₀ →
        ((r (((Mod R).selfChart hne).symm z) : R.retract) : E 0) = S z := by
      intro z hz
      have hzV : (⟨z, hz.1⟩ : R.retract) ∈ V :=
        show z ∈ S.U by rw [hSW]; exact ⟨hz.2, hOC hz.1⟩
      rw [(Mod R).selfChart_symm_apply hne hz.1]
      exact hr _ hzV
    refine (isScSmoothRetractMap_iff_exists hret).2
      ⟨fun z hz => ?_, R.restrict hW₀, R.restrict_retract hW₀, ?_⟩
    · change ((r (((Mod R).selfChart hne).symm z) : R.retract) : E 0) ∈ R.retract
      rw [heq z hz]
      exact hSO ⟨z, hz.1⟩ (show z ∈ S.U by rw [hSW]; exact ⟨hz.2, hOC hz.1⟩)
    · have hmaps : MapsTo (R.restrict hW₀) (R.restrict hW₀).U S.U := fun w hw => by
        have := (R.restrict hW₀).apply_mem_retract hw
        rw [R.restrict_retract hW₀] at this
        rw [hSW]; exact ⟨this.2, R.retract_subset_C this.1⟩
      have h1 : IsScSmooth (R.restrict hW₀).U (S ∘ R.restrict hW₀) :=
        IsScSmooth.comp (R.restrict hW₀).isScDomain S.isScDomain S.isScSmooth
          (R.restrict hW₀).isScSmooth hmaps
      refine h1.congr (R.restrict hW₀).isScDomain fun w hw => ?_
      have := (R.restrict hW₀).apply_mem_retract hw
      rw [R.restrict_retract hW₀] at this
      exact (heq _ this).symm
  · change (r y : E 0) ∈ S.U
    rw [hr y hy]; exact S.mapsTo hy
  · apply Subtype.ext
    have hry : (r y : E 0) ∈ S.U := by rw [hr y hy]; exact S.mapsTo hy
    rw [hr _ hry, hr y hy, S.idem _ hy]
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(hFG _).2 ?_, ?_⟩
      · rw [hr z hz, ← hSret]; exact S.apply_mem_retract hz
      · change (r z : E 0) ∈ S.U
        rw [hr z hz]; exact S.mapsTo hz
    · rintro ⟨hyF, hyV⟩
      refine ⟨y, hyV, Subtype.ext ?_⟩
      rw [hr y hyV]
      have : (y : E 0) ∈ S.retract := by rw [hSret]; exact (hFG y).1 hyF
      exact S.apply_eq_self_of_mem_retract this

theorem A'_to_B : A' → B := by
  intro hA E C R hne hTame F hF
  obtain ⟨h243, -, -, hsubF, -, -, -, htame⟩ := hA
  obtain ⟨n, W, T, hT⟩ := R.relOpen.isPartialQuadrant
  have hR := hTame n W T hT
  have hG : R.IsRetractFace (Subtype.val '' F) :=
    ((Mod R).isFace_toMPolyfold_iff hne R rfl hT hR F).1 hF
  obtain ⟨i, -, S, hGS, hSU, hSret, -⟩ := h243 hT hR hG
  refine ⟨⟨S, hSU, hGS, hSret, subData_of R hne S hSret⟩, ?_⟩
  have hsub := hsubF (Mod R) hne R rfl hT hR hF
  have hpc : ParacompactSpace F := ((Mod R).toMPolyfold hne).paracompactSpace_subtype F
  exact ⟨hsub, hpc, htame (Mod R) hne R rfl hT hR hF hsub hpc⟩

theorem A_to_B : A → B := fun h => A'_to_B (A_to_A' h)

/-! ### `B → A` (partial) -/

/-- `B` gives `LocalModel.isSubMPolyfold_of_isFace`. -/
theorem B_to_isSubMPolyfold (hB : B) : type_of% @Polyfold.LocalModel.isSubMPolyfold_of_isFace := by
  intro M hne n W R hRM T hT hR F hF
  cases M with
  | mk E C O hO =>
    dsimp only at R hT hR hne F hF hRM ⊢
    subst hRM
    exact ((hB E C R hne (hR.isTame hT) F hF).2).1

/-- `B` gives `proposition_2_5_15_isTame`, for any sub-M-polyfold proof and paracompactness
instance (i.e. `IsTame'`). -/
theorem B_to_isTame (hB : B) : IsTame' := by
  intro M hne n W R hRM T hT hR F hF hsub hpc
  cases M with
  | mk E C O hO =>
    dsimp only at R hT hR hne F hF hRM hsub hpc ⊢
    subst hRM
    obtain ⟨-, _, _, h⟩ := hB E C R hne (hR.isTame hT) F hF
    exact h

#rt_check RoundTrip.V2_49.A'_to_B [Polyfold.proposition_2_5_15, Polyfold.killCoord_mem,
  Polyfold.killCoord_eq_self, Polyfold.LocalModel.isSubMPolyfold_of_isFace,
  Polyfold.degIndexWith_eq_quadrantDeg_faceProj_add_one, Polyfold.proposition_2_5_15_tameModel,
  Polyfold.MPolyfold.faceChart_compatible_subChart, Polyfold.LocalModel.proposition_2_5_15_isTame]
#rt_check RoundTrip.V2_49.B_to_isSubMPolyfold [Polyfold.proposition_2_5_15, Polyfold.killCoord_mem,
  Polyfold.killCoord_eq_self, Polyfold.LocalModel.isSubMPolyfold_of_isFace,
  Polyfold.degIndexWith_eq_quadrantDeg_faceProj_add_one, Polyfold.proposition_2_5_15_tameModel,
  Polyfold.MPolyfold.faceChart_compatible_subChart, Polyfold.LocalModel.proposition_2_5_15_isTame]
#rt_check RoundTrip.V2_49.B_to_isTame [Polyfold.proposition_2_5_15, Polyfold.killCoord_mem,
  Polyfold.killCoord_eq_self, Polyfold.LocalModel.isSubMPolyfold_of_isFace,
  Polyfold.degIndexWith_eq_quadrantDeg_faceProj_add_one, Polyfold.proposition_2_5_15_tameModel,
  Polyfold.MPolyfold.faceChart_compatible_subChart, Polyfold.LocalModel.proposition_2_5_15_isTame]

end RoundTrip.V2_49
