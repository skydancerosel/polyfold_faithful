import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_7

/-! Round trip for V2_7 (Theorem 2.8: the chain rule for sc-smooth maps between retracts).

`A` is the conjunction of the types of `Polyfold.theorem_2_8`, `Polyfold.IsScSmoothRetractMap.comp`,
`Polyfold.retractTangentMap_comp`, `Polyfold.isScSmoothRetractMap_id`,
`Polyfold.ScRetraction.isScSmoothRetractMap` and `Polyfold.IsScSmoothRetractMap.congr`.  None has
universe parameters (`ScBanach` lives in `Type`), so no instantiation is needed.

`A → B`: B's `IsScSmoothB` (sc-smooth for SOME retraction) is upgraded to the project's
`IsScSmoothRetractMap` (for EVERY retraction) by Proposition 2.6 (1)
(`isScSmoothRetractMap_iff_exists`); the conclusions of B are then `theorem_2_8` read through
`retractTangentMap_eqOn` (the project's `Tf` is `T(f ∘ r)` on `TO`, for any `r`).

`B → A`: B assumes `O''` is a retract, which `theorem_2_8` does not; this is removed by applying B
with the target retract `(E''₀, E''₀, E'')` (`C'' = O'' = univ`, retraction `id`) and getting
`(g ∘ f)(O) ⊆ O''` from the hypotheses directly.  The project's `retractTangentMap` / `retractTangent`
unfold to `T(· ∘ r)` / `Tr(TU)` for the chosen retraction `hO.choose`, an instance of B's
"for every retraction".  `IsScSmoothRetractMap.comp` (no hypothesis that `O` is a retract) is
vacuous on the `∀ R` part when `O` is not a retract.  The three auxiliary conjuncts (`id`, the
retraction itself, `congr`) are not part of Theorem 2.8 and are proved directly from the project's
definitions (sc-smooth composition and `IsScSmooth.congr`), without B. -/

namespace RoundTrip.V2_7
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.theorem_2_8) ∧ (type_of% @Polyfold.IsScSmoothRetractMap.comp) ∧
    (type_of% @Polyfold.retractTangentMap_comp) ∧ (type_of% @Polyfold.isScSmoothRetractMap_id) ∧
    (type_of% @Polyfold.ScRetraction.isScSmoothRetractMap) ∧
    (type_of% @Polyfold.IsScSmoothRetractMap.congr)

theorem A_holds : A :=
  ⟨@Polyfold.theorem_2_8, @Polyfold.IsScSmoothRetractMap.comp, @Polyfold.retractTangentMap_comp,
    @Polyfold.isScSmoothRetractMap_id, @Polyfold.ScRetraction.isScSmoothRetractMap,
    @Polyfold.IsScSmoothRetractMap.congr⟩

/-- The blind "sc-smooth for some retraction" is the project's notion (Proposition 2.6 (1)). -/
theorem isScSmoothB_iff {E E' : ScBanach} {C O : Set (E.lvl 0)} {C' O' : Set (E'.lvl 0)}
    {f : E.lvl 0 → E'.lvl 0} (hO : IsScRetract E C O) :
    IsScSmoothB E C O E' O' f ↔ IsScSmoothRetractMap E C O E' C' O' f :=
  (isScSmoothRetractMap_iff_exists hO).symm

theorem A_to_B : A → B := by
  intro hA E E' E'' C O C' O' C'' O'' f g hO hO' _ hf hg
  have hf' : IsScSmoothRetractMap E C O E' C' O' f := (isScSmoothB_iff hO).1 hf
  have hg' : IsScSmoothRetractMap E' C' O' E'' C'' O'' g := (isScSmoothB_iff hO').1 hg
  obtain ⟨hgf, hT⟩ := hA.1 hO hO' hf' hg'
  refine ⟨⟨hgf.mapsTo, hgf.comp_isScSmooth⟩, ?_⟩
  intro R hR R' hR' p hp
  have hp' : p ∈ retractTangent E C O := by rw [← hR, retractTangent_eq]; exact hp
  have hTf : retractTangentMap E C O f p ∈ retractTangent E' C' O' :=
    hf'.tangentMap_mapsTo hO hO' hp'
  have h1 := retractTangentMap_eqOn hgf R hR hp'
  have h2 := retractTangentMap_eqOn hg' R' hR' hTf
  have h3 := retractTangentMap_eqOn hf' R hR hp'
  rw [← h1, hT hp', Function.comp_apply, h2, h3]

/-- `(E''₀, E''₀, E'')` is a retract (the identity retraction). -/
theorem isScRetract_univ (E : ScBanach) : IsScRetract E univ univ :=
  IsRelOpenInQuadrant.isScRetract ⟨isPartialQuadrant_univ E, univ, isOpen_univ, (inter_univ _).symm⟩

/-- The chain rule from B, without assuming that `O''` is a retract. -/
theorem chain_of_B (hB : B) {E E' E'' : ScBanach} {C O : Set (E.lvl 0)} {C' O' : Set (E'.lvl 0)}
    {C'' O'' : Set (E''.lvl 0)} {f : E.lvl 0 → E'.lvl 0} {g : E'.lvl 0 → E''.lvl 0}
    (hO : IsScRetract E C O) (hO' : IsScRetract E' C' O')
    (hf : IsScSmoothRetractMap E C O E' C' O' f) (hg : IsScSmoothRetractMap E' C' O' E'' C'' O'' g) :
    IsScSmoothRetractMap E C O E'' C'' O'' (g ∘ f) ∧
      (∀ R : ScRetraction E C, R.retract = O → ∀ R' : ScRetraction E' C', R'.retract = O' →
        ∀ p ∈ R.tangent,
          tangentMap R.U ((g ∘ f) ∘ R.toFun) p =
            tangentMap R'.U (g ∘ R'.toFun) (tangentMap R.U (f ∘ R.toFun) p)) := by
  obtain ⟨R₀, hR₀⟩ := hO
  obtain ⟨R₀', hR₀'⟩ := hO'
  have h := hB E E' E'' C O C' O' univ univ f g ⟨R₀, hR₀⟩ ⟨R₀', hR₀'⟩ (isScRetract_univ E'')
    ⟨hf.mapsTo, R₀, hR₀, hf.comp_isScSmooth R₀ hR₀⟩
    ⟨mapsTo_univ _ _, R₀', hR₀', hg.comp_isScSmooth R₀' hR₀'⟩
  exact ⟨⟨hg.mapsTo.comp hf.mapsTo, h.1.2⟩, h.2⟩

theorem B_to_A : B → A := by
  intro hB
  have h28 : type_of% @Polyfold.theorem_2_8 := by
    intro E E' E'' C C' C'' f g O O' O'' hO hO' hf hg
    obtain ⟨h1, h2⟩ := chain_of_B hB hO hO' hf hg
    refine ⟨h1, ?_⟩
    intro p hp
    simp only [retractTangentMap, retractTangent, dif_pos hO, dif_pos hO'] at hp ⊢
    exact h2 hO.choose hO.choose_spec hO'.choose hO'.choose_spec p hp
  refine ⟨h28, ?_, ?_, ?_, ?_, ?_⟩
  · intro E E' E'' C C' C'' f g O O' O'' hg hf hO'
    by_cases hO : IsScRetract E C O
    · exact (h28 hO hO' hf hg).1
    · exact ⟨hg.mapsTo.comp hf.mapsTo, fun R hR => absurd ⟨R, hR⟩ hO⟩
  · intro E E' E'' C C' C'' f g O O' O'' hg hf hO hO'
    exact (h28 hO hO' hf hg).2
  · intro E C O
    exact ⟨mapsTo_id O, fun R _ => R.isScSmooth⟩
  · intro E C R
    refine ⟨R.mapsTo_retract, fun S hS => ?_⟩
    have hmaps : MapsTo S S.U R.U := fun y hy => hS ▸ S.apply_mem_retract hy
    exact IsScSmooth.comp S.isScDomain R.isScDomain R.isScSmooth S.isScSmooth hmaps
  · intro E E' C C' f O O' hf f' hff'
    exact ⟨fun _ hx => hff' hx ▸ hf.mapsTo hx, fun R hR =>
      (hf.comp_isScSmooth R hR).congr R.isScDomain fun _ hy => hff' (hR ▸ R.apply_mem_retract hy)⟩

#rt_check RoundTrip.V2_7.A_to_B [Polyfold.theorem_2_8, Polyfold.IsScSmoothRetractMap.comp,
  Polyfold.retractTangentMap_comp, Polyfold.isScSmoothRetractMap_id,
  Polyfold.ScRetraction.isScSmoothRetractMap, Polyfold.IsScSmoothRetractMap.congr]
#rt_check RoundTrip.V2_7.B_to_A [Polyfold.theorem_2_8, Polyfold.IsScSmoothRetractMap.comp,
  Polyfold.retractTangentMap_comp, Polyfold.isScSmoothRetractMap_id,
  Polyfold.ScRetraction.isScSmoothRetractMap, Polyfold.IsScSmoothRetractMap.congr]
#rt_overlap RoundTrip.V2_7.B_to_A [Polyfold.theorem_2_8, Polyfold.IsScSmoothRetractMap.comp,
  Polyfold.retractTangentMap_comp, Polyfold.isScSmoothRetractMap_id,
  Polyfold.ScRetraction.isScSmoothRetractMap, Polyfold.IsScSmoothRetractMap.congr]

end RoundTrip.V2_7
