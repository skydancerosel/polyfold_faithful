import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_40

/-! Round trip for V2_40 (Definition 2.34: tame retractions and tame retracts).

`A` is the conjunction of the types of `Polyfold.IsTameRetract.isScRetract`,
`ScRetraction.id_isTame`, `ScRetraction.IsTameWith.isTame` and `ScRetraction.IsTameWith.restrict`
(no universe parameters).  `ScRetraction.IsTameWith`, `ScRetraction.IsTame` and `IsTameRetract`
are definitions (vocabulary).

The definitions agree with B's (`isTameWith_iff`): for a presentation `T` of `C`,
`R.IsTameWith T ↔ IsTameWithB R T`.  (1) `degIndex E C = degIndexWith T = dCB T` on `C ⊇ U`
(`degIndex_eq`, `dCB_eq`).  (2) The project's "`x : E 1` with `ι₁x ∈ O` and `x ∈ E_∞`" is B's
"`x ∈ O ∩ E_∞` with a lift `x₁`"; `minimalSubspaceWith T x = ExB T x` (`ExB_eq`); B's extra clause
"`A` is an sc-subspace" is part of the project's `IsScSplitting`.  Both `IsTame` and `IsTameB`
quantify over every presentation; `IsTameRetract` and `IsTameRetractB` are then the same
existential.  So B holds outright and `A → B` does not use A.

`B → A` is proved only outright (B unused): A's four lemmas are properties of the definitions
(a tame retract is a retract; the identity of a relatively open `U` is tame; tameness for ONE
presentation implies tameness for all — presentation independence, via the project's
`minimalSubspaceWith_eq`, the sign argument of Lemma 1.24; restriction to `U ∩ r⁻¹(V)` preserves
tameness), none of which B states.  They are re-proved here from non-item project lemmas. -/

namespace RoundTrip.V2_40
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.IsTameRetract.isScRetract) ∧ (type_of% @Polyfold.ScRetraction.id_isTame) ∧
    (type_of% @Polyfold.ScRetraction.IsTameWith.isTame) ∧
    (type_of% @Polyfold.ScRetraction.IsTameWith.restrict)

theorem A_holds : A :=
  ⟨@Polyfold.IsTameRetract.isScRetract, @Polyfold.ScRetraction.id_isTame,
    @Polyfold.ScRetraction.IsTameWith.isTame, @Polyfold.ScRetraction.IsTameWith.restrict⟩

/-! ### Glue: the project's notions are B's -/

section Glue

variable {E : ScBanach} {C : Set (E 0)} {n : ℕ} {W : ScBanach}

lemma lamB_apply (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (i : Fin n) (v : E 0) :
    lamB T i v = (T 0 v).1 i := rfl

lemma dCB_eq (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x : E 0) :
    dCB T x = degIndexWith T x := by
  classical
  rw [dCB, degIndexWith, quadrantDeg, ← Set.ncard_coe_finset]
  congr 1
  ext i
  simp [lamB_apply]

lemma ExB_eq (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (x : E 0) :
    ExB T x = minimalSubspaceWith T x := by
  ext v
  rw [mem_minimalSubspaceWith, ExB]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, lamB_apply]
  rfl

theorem isTameWith_iff (R : ScRetraction E C) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : C = T 0 ⁻¹' quadrant n W 0) : R.IsTameWith T ↔ IsTameWithB R T := by
  have hdeg : ∀ y ∈ R.U, degIndex E C y = dCB T y := fun y hy => by
    rw [dCB_eq, degIndex_eq T hT (R.U_subset_C hy)]
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun x hx hxs x₁ hx₁ => ?_⟩
    · rw [← hdeg x hx, ← hdeg _ (R.mapsTo hx)]
      exact h.degIndex_apply x hx
    · have h1 : x₁ ∈ E.lvlSet R.retract 1 := by rw [ScBanach.mem_lvlSet, hx₁]; exact hx
      have h2 : x₁ ∈ E.smoothLvl 1 := by
        change E.toBase 1 x₁ ∈ (E.smooth : Set (E 0)); rw [hx₁]; exact hxs
      obtain ⟨A, hA, hAE⟩ := h.exists_complement x₁ h1 h2
      refine ⟨A, hA.2.1, ?_, hA⟩
      rw [ExB_eq, ← hx₁]; exact hAE
  · intro h
    refine ⟨fun x hx => ?_, fun x hx hxs => ?_⟩
    · rw [hdeg x hx, hdeg _ (R.mapsTo hx)]
      exact h.1 x hx
    · obtain ⟨A, _, hAE, hA⟩ := h.2 (E.toBase 1 x) hx hxs x rfl
      refine ⟨A, hA, ?_⟩
      rw [← ExB_eq]; exact hAE

end Glue

/-- B holds outright: the project's definitions are B's. -/
theorem B_holds : B := by
  refine ⟨fun E C R => ⟨fun h n W T hT => (isTameWith_iff R T hT).1 (h n W T hT),
    fun h n W T hT => (isTameWith_iff R T hT).2 (h n W T hT)⟩, fun E C O => ?_⟩
  have key : ∀ R : ScRetraction E C, R.IsTame ↔ IsTameB R := fun R =>
    ⟨fun h n W T hT => (isTameWith_iff R T hT).1 (h n W T hT),
      fun h n W T hT => (isTameWith_iff R T hT).2 (h n W T hT)⟩
  constructor
  · rintro ⟨R, hR, ht⟩; exact ⟨R, hR, (key R).1 ht⟩
  · rintro ⟨R, hR, ht⟩; exact ⟨R, hR, (key R).2 ht⟩

/-- `A → B`: B holds outright (A unused). -/
theorem A_to_B : A → B := fun _ => B_holds

/-! ### `B → A`, outright (B is not used) -/

section Outright

variable {E : ScBanach} {C : Set (E 0)} {n n'' : ℕ} {W W'' : ScBanach}

theorem isScRetract_outright {O : Set (E 0)} (h : IsTameRetract E C O) : IsScRetract E C O := by
  obtain ⟨R, hR, _⟩ := h
  exact ⟨R, hR⟩

theorem id_isTame_outright {U : Set (E 0)} (hU : IsRelOpenInQuadrant E C U) :
    (ScRetraction.id hU).IsTame := by
  intro n W T hT
  refine ⟨fun _ _ => rfl, fun x hx _ => ⟨⊥, ?_, bot_le⟩⟩
  have hret : (ScRetraction.id hU).retract = U := image_id U
  have hxU : x ∈ E.lvlSet U 1 := by rw [← hret]; exact hx
  have hD : scDeriv (ScRetraction.id hU).U (ScRetraction.id hU) x = ContinuousLinearMap.id ℝ (E 0) :=
    IsSc1.scDeriv_eqOn (isSc1With_id U) (hU.isScDomain.uniqueDiffWithinAt 1) hxU
  have hrange : LinearMap.range (scDeriv (ScRetraction.id hU).U (ScRetraction.id hU) x :
      E 0 →ₗ[ℝ] E 0) = ⊤ := by
    rw [hD]; exact LinearMap.range_id
  rw [hrange]
  refine ⟨⟨by rw [Submodule.top_coe]; exact isClosed_univ, fun m => ?_⟩,
    ⟨by rw [Submodule.bot_coe]; exact isClosed_singleton, fun m => ?_⟩, fun m => ?_⟩
  · intro y _
    have : (E.levelSub ⊤ m : Set (E m)) ∩ E.smoothLvl m = E.smoothLvl m := by
      ext z; simp [ScBanach.mem_levelSub]
    rw [this, (E.dense_smooth m).closure_eq]; exact mem_univ _
  · intro y hy
    have hy0 : y = 0 := by
      have : E.toBase m y ∈ (⊥ : Submodule ℝ (E 0)) := hy
      rw [Submodule.mem_bot] at this
      exact E.toBase_injective m (by rw [this, map_zero])
    subst hy0
    refine subset_closure ⟨(E.levelSub ⊥ m).zero_mem, ?_⟩
    change E.toBase m 0 ∈ E.smooth
    rw [map_zero]; exact E.smooth.zero_mem
  · have h1 : E.levelSub ⊤ m = ⊤ := by ext z; simp [ScBanach.mem_levelSub]
    have h2 : E.levelSub ⊥ m = ⊥ := by
      ext z
      simp only [ScBanach.mem_levelSub, Submodule.mem_bot]
      exact ⟨fun h => E.toBase_injective m (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
    rw [h1, h2]; exact isCompl_top_bot

theorem isTame_outright {R : ScRetraction E C}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} (hT : C = T 0 ⁻¹' quadrant n W 0)
    (h : R.IsTameWith T) : R.IsTame := by
  intro n'' W'' T'' hT''
  refine ⟨h.degIndex_apply, fun x hx hs => ?_⟩
  obtain ⟨A, hA, hAE⟩ := h.exists_complement x hx hs
  refine ⟨A, hA, ?_⟩
  rw [← minimalSubspaceWith_eq T hT T'' hT'' (R.retract_subset_C hx)]
  exact hAE

theorem restrict_outright {R : ScRetraction E C}
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} (h : R.IsTameWith T) {V : Set (E 0)}
    (hV : IsOpen V) : (R.restrict hV).IsTameWith T where
  degIndex_apply x hx := h.degIndex_apply x hx.1
  exists_complement x hx hs := by
    have hx' : x ∈ E.lvlSet R.retract 1 := by
      have : E.toBase 1 x ∈ (R.restrict hV).retract := hx
      rw [R.restrict_retract] at this; exact this.1
    rw [R.scDeriv_restrict hV ((R.restrict hV).lvlSet_retract_subset 1 hx)]
    exact h.exists_complement x hx' hs

end Outright

theorem B_to_A : B → A := fun _ =>
  ⟨@isScRetract_outright, @id_isTame_outright, @isTame_outright, @restrict_outright⟩

#rt_check RoundTrip.V2_40.A_to_B [Polyfold.IsTameRetract.isScRetract,
  Polyfold.ScRetraction.id_isTame, Polyfold.ScRetraction.IsTameWith.isTame,
  Polyfold.ScRetraction.IsTameWith.restrict]
#rt_check RoundTrip.V2_40.B_to_A [Polyfold.IsTameRetract.isScRetract,
  Polyfold.ScRetraction.id_isTame, Polyfold.ScRetraction.IsTameWith.isTame,
  Polyfold.ScRetraction.IsTameWith.restrict]
#rt_overlap RoundTrip.V2_40.B_to_A [Polyfold.IsTameRetract.isScRetract,
  Polyfold.ScRetraction.id_isTame, Polyfold.ScRetraction.IsTameWith.isTame,
  Polyfold.ScRetraction.IsTameWith.restrict]

end RoundTrip.V2_40
