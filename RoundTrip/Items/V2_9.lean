import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_9

/-! Round trip for V2_9 (Proposition 2.10: open subsets of retracts, and images of sc-smooth
idempotents on them, are retracts).

`A` is the conjunction of the types of `Polyfold.proposition_2_10_1`,
`Polyfold.proposition_2_10_2`, `Polyfold.ScRetraction.restrict_retract`,
`Polyfold.IsScSmoothRetractMap.restrict` and `Polyfold.IsScSmoothRetractMap.of_locally` (no
universe parameters: `ScBanach` lives in `Type`).  `ScRetraction.restrict` and
`LocalModel.restrict` are definitions (vocabulary).

`A → B`: (1) is `proposition_2_10_1`.  (2): `V = O ∩ W` is a retract by (1), and B's existential
hypothesis on `s` is the project's `IsScSmoothRetractMap E C V E C V s` by
`isScSmoothRetractMap_iff_exists` (item V2_6, not banned here); then `proposition_2_10_2`.

`B → A`: `proposition_2_10_1` is B (1) with `O' = O ∩ W`; `proposition_2_10_2` is B (2) with
`O := V`, `W := univ` (B's hypothesis "for some retraction" follows from the project's "for every
retraction").  The other three conjuncts (`restrict_retract`: `r(U ∩ r⁻¹W) = r(U) ∩ W`;
`IsScSmoothRetractMap.restrict`: restriction of an sc-smooth map to `O ∩ W`; and
`IsScSmoothRetractMap.of_locally`: sc-smoothness between retracts is local) are proof
infrastructure, not in the text's statement nor in B; they are re-proved directly (the project's
arguments), without B. -/

namespace RoundTrip.V2_9
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.proposition_2_10_1) ∧
    (type_of% @Polyfold.proposition_2_10_2) ∧
    (type_of% @Polyfold.ScRetraction.restrict_retract) ∧
    (type_of% @Polyfold.IsScSmoothRetractMap.restrict) ∧
    (type_of% @Polyfold.IsScSmoothRetractMap.of_locally)

theorem A_holds : A :=
  ⟨@Polyfold.proposition_2_10_1, @Polyfold.proposition_2_10_2,
    @Polyfold.ScRetraction.restrict_retract, @Polyfold.IsScSmoothRetractMap.restrict,
    @Polyfold.IsScSmoothRetractMap.of_locally⟩

theorem A_to_B : A → B := by
  rintro ⟨h1, h2, -, -, -⟩ E C O hO
  refine ⟨?_, ?_⟩
  · rintro O' ⟨W, hW, rfl⟩
    exact h1 hO hW
  · rintro V ⟨W, hW, rfl⟩ s hs hss
    have hV : IsScRetract E C (O ∩ W) := h1 hO hW
    exact h2 hV ((isScSmoothRetractMap_iff_exists hV).2 hs) hss

/-! ### Direct proofs of the infrastructure conjuncts -/

theorem restrict_retract' {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C) {W : Set (E 0)}
    (hW : IsOpen W) : (R.restrict hW).retract = R.retract ∩ W := by
  ext z
  constructor
  · rintro ⟨y, ⟨hy, hyW⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, hyW⟩
  · rintro ⟨⟨y, hy, rfl⟩, hzW⟩
    exact ⟨y, ⟨hy, hzW⟩, rfl⟩

theorem restrict' {E E' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)} {O : Set (E 0)}
    {O' : Set (E' 0)} {f : E 0 → E' 0} (hf : IsScSmoothRetractMap E C O E' C' O' f)
    (hO : IsScRetract E C O) {W : Set (E 0)} : IsScSmoothRetractMap E C (O ∩ W) E' C' O' f where
  mapsTo := hf.mapsTo.mono_left inter_subset_left
  comp_isScSmooth S hS := by
    obtain ⟨R, rfl⟩ := hO
    have hmem : ∀ y ∈ S.U, S.toFun y ∈ R.retract ∩ W := fun y hy => hS ▸ S.apply_mem_retract hy
    have hfix : ∀ y ∈ S.U, R.toFun (S.toFun y) = S.toFun y := fun y hy =>
      R.apply_eq_self_of_mem_retract (hmem y hy).1
    have hmaps : MapsTo S.toFun S.U R.U := fun y hy => R.retract_subset (hmem y hy).1
    have := IsScSmooth.comp S.isScDomain R.isScDomain (hf.comp_isScSmooth R rfl) S.isScSmooth hmaps
    refine this.congr S.isScDomain fun y hy => ?_
    simp only [Function.comp_apply, hfix y hy]

theorem of_locally' {E E' : ScBanach} {C : Set (E 0)} {C' : Set (E' 0)} {O : Set (E 0)}
    {O' : Set (E' 0)} {f : E 0 → E' 0} (hmaps : MapsTo f O O')
    (h : ∀ x ∈ O, ∃ W : Set (E 0), IsOpen W ∧ x ∈ W ∧ IsScSmoothRetractMap E C (O ∩ W) E' C' O' f) :
    IsScSmoothRetractMap E C O E' C' O' f where
  mapsTo := hmaps
  comp_isScSmooth R hR := by
    refine IsScSmooth.of_locally R.isScDomain fun y hy => ?_
    obtain ⟨W, hWo, hxW, hW⟩ := h (R y) (hR ▸ (⟨y, hy, rfl⟩ : R.toFun y ∈ R.retract))
    obtain ⟨u, hu, huU⟩ := (continuousOn_iff'.1 R.isSc1.isSc0.continuousOn_base) W hWo
    refine ⟨u, hu, ?_, ?_⟩
    · have : y ∈ R ⁻¹' W ∩ R.U := ⟨hxW, hy⟩
      rw [huU] at this; exact this.1
    · have hUu : R.U ∩ u = (R.restrict hWo).U := by
        rw [ScRetraction.restrict_U, inter_comm R.U (R ⁻¹' W), huU, inter_comm]
      rw [hUu]
      have hRW : (R.restrict hWo).retract = O ∩ W := by rw [restrict_retract' R hWo, hR]
      have hsub : MapsTo R (R.restrict hWo).U (R.restrict hWo).U := (R.restrict hWo).mapsTo
      have h1 := hW.comp_isScSmooth (R.restrict hWo) hRW
      have := IsScSmooth.comp (R.restrict hWo).isScDomain (R.restrict hWo).isScDomain h1
        (R.restrict hWo).isScSmooth hsub
      refine this.congr (R.restrict hWo).isScDomain fun z hz => ?_
      change f (R (R z)) = f (R z)
      rw [R.idem z hz.1]

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, fun R W hW => restrict_retract' R hW, @restrict', @of_locally'⟩
  · intro E C O hO W hW
    exact (hB E C O hO).1 (O ∩ W) ⟨W, hW, rfl⟩
  · intro E C V hV s hs hss
    obtain ⟨R, hR⟩ := hV
    exact (hB E C V ⟨R, hR⟩).2 V ⟨univ, isOpen_univ, (inter_univ V).symm⟩ s
      ⟨hs.mapsTo, R, hR, hs.comp_isScSmooth R hR⟩ hss

#rt_check RoundTrip.V2_9.A_to_B [Polyfold.proposition_2_10_1, Polyfold.proposition_2_10_2,
  Polyfold.ScRetraction.restrict_retract, Polyfold.IsScSmoothRetractMap.restrict,
  Polyfold.IsScSmoothRetractMap.of_locally]
#rt_check RoundTrip.V2_9.B_to_A [Polyfold.proposition_2_10_1, Polyfold.proposition_2_10_2,
  Polyfold.ScRetraction.restrict_retract, Polyfold.IsScSmoothRetractMap.restrict,
  Polyfold.IsScSmoothRetractMap.of_locally]
#rt_overlap RoundTrip.V2_9.B_to_A [Polyfold.proposition_2_10_1, Polyfold.proposition_2_10_2,
  Polyfold.ScRetraction.restrict_retract, Polyfold.IsScSmoothRetractMap.restrict,
  Polyfold.IsScSmoothRetractMap.of_locally]

end RoundTrip.V2_9
