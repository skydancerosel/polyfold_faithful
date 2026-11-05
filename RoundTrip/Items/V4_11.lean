import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_11

/-!
Round trip for V4_11 (Definition 4.6, sc⁺-retracts, and the remark that the notion is intrinsic).
The decls list one definition (`IsScPlusRetract`, vocabulary) and two theorems, so `A` is the
conjunction of the types of `Polyfold.IsScPlusRetract.isScPlus` and
`Polyfold.isScPlusRetract_iff_forall` (no universe parameters).

Glue (`isScPlus_iff`, as in V4_9): the project's `R.IsScPlus = IsScPlus R.U R` (the canonical lift
`E.liftOne ∘ R` is sc-smooth into `E¹`) agrees with B's `IsScPlusRetractionB R`
(`r(U_m) ⊆ E_{m+1}` and SOME lift `g : E₀ → E₁` of `r` on `U` sc-smooth into `E¹`), by
`IsScPlus.iff_exists` and `ScRetraction.IsScPlus.mem_lvlSet_succ`.  This gives B's first conjunct
(`IsScPlusRetract ↔ IsScPlusRetractB`) without A; B's second conjunct ("intrinsic") is A's first
conjunct.  Conversely B gives `IsScPlusRetract.isScPlus` from its second conjunct, and
`isScPlusRetract_iff_forall` is then a repackaging.
-/

namespace RoundTrip.V4_11
open Polyfold

def A : Prop :=
  type_of% @Polyfold.IsScPlusRetract.isScPlus ∧ type_of% @Polyfold.isScPlusRetract_iff_forall

theorem A_holds : A := ⟨@Polyfold.IsScPlusRetract.isScPlus, @Polyfold.isScPlusRetract_iff_forall⟩

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

/-- The definitions agree (independent of A). -/
theorem isScPlusRetract_iff (E : ScBanach) (C O : Set (E.lvl 0)) :
    IsScPlusRetract E C O ↔ IsScPlusRetractB E C O := by
  constructor
  · rintro ⟨R, hR, hp⟩; exact ⟨R, hR, (isScPlus_iff R).1 hp⟩
  · rintro ⟨R, hR, hp⟩; exact ⟨R, hR, (isScPlus_iff R).2 hp⟩

theorem A_to_B : A → B := by
  rintro ⟨hA1, -⟩
  refine ⟨isScPlusRetract_iff, fun E C O h s hs => ?_⟩
  exact (isScPlus_iff s).1 (hA1 ((isScPlusRetract_iff E C O).2 h) s hs)

theorem B_to_A : B → A := by
  rintro ⟨hB1, hB2⟩
  have h1 : ∀ {E : ScBanach} {C O : Set (E.lvl 0)}, IsScPlusRetract E C O →
      ∀ (S : ScRetraction E C), S.retract = O → S.IsScPlus := fun {E C O} h S hS =>
    (isScPlus_iff S).2 (hB2 E C O ((hB1 E C O).1 h) S hS)
  refine ⟨@h1, fun {E C O} => ⟨fun h => ?_, ?_⟩⟩
  · obtain ⟨R, hR, hp⟩ := h
    exact ⟨⟨R, hR⟩, h1 ⟨R, hR, hp⟩⟩
  · rintro ⟨⟨R, hR⟩, h⟩
    exact ⟨R, hR, h R hR⟩

#rt_check RoundTrip.V4_11.A_to_B [Polyfold.IsScPlusRetract.isScPlus, Polyfold.isScPlusRetract_iff_forall]
#rt_check RoundTrip.V4_11.B_to_A [Polyfold.IsScPlusRetract.isScPlus, Polyfold.isScPlusRetract_iff_forall]
#rt_overlap RoundTrip.V4_11.B_to_A [Polyfold.IsScPlusRetract.isScPlus, Polyfold.isScPlusRetract_iff_forall]

end RoundTrip.V4_11
