import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_13

/-!
Round trip for V4_13 (Proposition 4.8: an sc-smooth retract `(O, C, E)` is an sc⁺-retract iff
`O₀ = O_∞` and `1₀¹ : O → O¹` is sc-smooth).  `A` is the type of `Polyfold.proposition_4_8` (no
universe parameters).

Glue:
* sc⁺-retract: the project's `IsScPlusRetract` is B's `IsScPlusRetractB` (`isScPlus_iff`, as in
  V4_9/V4_11: `IsScPlus.iff_exists` and `ScRetraction.IsScPlus.mem_lvlSet_succ`).
* `O ⊆ E_∞` is B's pointwise "lifts to every level" (`ScBanach.mem_smooth_iff`).
* `1₀¹`: A uses the canonical lift `E.liftOne` (a junk value off `E₁`), B every map `g : E₀ → E₁`
  with `ι₁ ∘ g = id` on `O`.  `IsScSmoothRetractMap` only sees `g` on `O` (the `mapsTo` clause) and
  `g ∘ R` on `R.U` with `R(R.U) = O`, so any two lifts on `O` give the same predicate
  (`retractMap_congr`, `IsScSmooth.congr`); `E.liftOne` is a lift on `O` once `O ⊆ E₁`.
-/

namespace RoundTrip.V4_13
open Polyfold

def A : Prop := type_of% @Polyfold.proposition_4_8

theorem A_holds : A := @Polyfold.proposition_4_8

/-- The project's `ScRetraction.IsScPlus` is B's Definition 4.4 (cf. V4_9). -/
theorem isScPlus_iff {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C) :
    R.IsScPlus ↔ IsScPlusRetractionB R := by
  constructor
  · intro hR
    refine ⟨fun m x hx => ?_, E.liftOne ∘ R, fun x hx => IsScPlus.toBase_lift hR hx,
      hR.isScSmooth_lift⟩
    obtain ⟨y, -, hy⟩ := hR.mem_lvlSet_succ m hx
    exact ⟨y, hy⟩
  · rintro ⟨-, g, hg, hgs⟩
    exact (IsScPlus.iff_exists R.isScDomain).2 ⟨g, hgs, hg⟩

theorem isScPlusRetract_iff (E : ScBanach) (C O : Set (E.lvl 0)) :
    IsScPlusRetract E C O ↔ IsScPlusRetractB E C O := by
  constructor
  · rintro ⟨R, hR, hp⟩; exact ⟨R, hR, (isScPlus_iff R).1 hp⟩
  · rintro ⟨R, hR, hp⟩; exact ⟨R, hR, (isScPlus_iff R).2 hp⟩

/-- Sc-smoothness between retracts only sees the lift on `O`. -/
theorem retractMap_congr {E : ScBanach} {C O : Set (E.lvl 0)} {g g' : E.lvl 0 → E.shift.lvl 0}
    (hg : ∀ x ∈ O, E.toBase 1 (g x) = x) (hg' : ∀ x ∈ O, E.toBase 1 (g' x) = x)
    (h : IsScSmoothRetractMap E C O E.shift (E.lvlSet C 1) (E.lvlSet O 1) g) :
    IsScSmoothRetractMap E C O E.shift (E.lvlSet C 1) (E.lvlSet O 1) g' := by
  have heq : ∀ x ∈ O, g x = g' x := fun x hx =>
    E.toBase_injective 1 ((hg x hx).trans (hg' x hx).symm)
  refine ⟨fun x hx => ?_, fun R hR => ?_⟩
  · rw [ScBanach.mem_lvlSet, hg' x hx]; exact hx
  · refine (h.comp_isScSmooth R hR).congr R.isScDomain fun x hx => ?_
    exact heq _ (hR ▸ R.apply_mem_retract hx)

lemma liftOne_lift {E : ScBanach} {O : Set (E.lvl 0)} (h : O ⊆ ↑E.smooth) :
    ∀ x ∈ O, E.toBase 1 (E.liftOne x) = x := fun _ hx =>
  E.toBase_liftOne (E.mem_smooth_iff.1 (h hx) 1)

theorem A_to_B : A → B := by
  intro hA E C O hO
  rw [← isScPlusRetract_iff, hA hO]
  constructor
  · rintro ⟨hsm, hmap⟩
    exact ⟨fun o ho => E.mem_smooth_iff.1 (hsm ho), fun g hg =>
      retractMap_congr (liftOne_lift hsm) hg hmap⟩
  · rintro ⟨hsm, hmap⟩
    have hsm' : O ⊆ ↑E.smooth := fun o ho => E.mem_smooth_iff.2 (hsm o ho)
    exact ⟨hsm', hmap _ (liftOne_lift hsm')⟩

theorem B_to_A : B → A := by
  intro hB E C O hO
  rw [isScPlusRetract_iff, hB E C O hO]
  constructor
  · rintro ⟨hsm, hmap⟩
    have hsm' : O ⊆ ↑E.smooth := fun o ho => E.mem_smooth_iff.2 (hsm o ho)
    exact ⟨hsm', hmap _ (liftOne_lift hsm')⟩
  · rintro ⟨hsm, hmap⟩
    exact ⟨fun o ho => E.mem_smooth_iff.1 (hsm ho), fun g hg =>
      retractMap_congr (liftOne_lift hsm) hg hmap⟩

#rt_check RoundTrip.V4_13.A_to_B [Polyfold.proposition_4_8]
#rt_check RoundTrip.V4_13.B_to_A [Polyfold.proposition_4_8]
#rt_overlap RoundTrip.V4_13.B_to_A [Polyfold.proposition_4_8]

end RoundTrip.V4_13
