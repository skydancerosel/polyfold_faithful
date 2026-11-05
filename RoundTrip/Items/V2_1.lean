import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_1

/-! Round trip for V2_1 (Definition 2.1: sc-smooth retractions; the remark after Definition 2.3:
`Dr(x)` is a projection for `x ∈ O₁`).

`A` is the conjunction of the types of `Polyfold.ScRetraction.mem_retract_iff`,
`Polyfold.ScRetraction.apply_eq_self_of_mem_retract`, `Polyfold.ScRetraction.lvlSet_retract_subset`
and `Polyfold.ScRetraction.scDeriv_comp_self` (no universe parameters: `ScBanach` lives in `Type`).
`ScRetraction` and `ScRetraction.retract` are definitions (vocabulary).

`A → B`: the definitional part of B (`ScRetraction` ↔ B's `IsScRetractionB`) is structure
packing/unpacking.  The projection claim for `x ∈ O₁` is `scDeriv_comp_self`.  B's chain-rule
claim `Dr(r(x)) ∘ Dr(x) = Dr(x)` for every `x ∈ U₁` is *not* in A (A has it only on `O₁`); it is
proved from the project's `ScRetraction.tangentMap_tangentMap` (`Tr ∘ Tr = Tr` on `TU`, the chain
rule `theorem_1_21` applied to `r ∘ r = r`), which is not an item theorem.

`B → A`: `scDeriv_comp_self` is B's projection claim; the other three conjuncts are elementary
facts about `r(U)` proved directly. -/

namespace RoundTrip.V2_1
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.ScRetraction.mem_retract_iff) ∧
    (type_of% @Polyfold.ScRetraction.apply_eq_self_of_mem_retract) ∧
    (type_of% @Polyfold.ScRetraction.lvlSet_retract_subset) ∧
    (type_of% @Polyfold.ScRetraction.scDeriv_comp_self)

theorem A_holds : A :=
  ⟨@Polyfold.ScRetraction.mem_retract_iff, @Polyfold.ScRetraction.apply_eq_self_of_mem_retract,
    @Polyfold.ScRetraction.lvlSet_retract_subset, @Polyfold.ScRetraction.scDeriv_comp_self⟩

/-- The retraction packaged from B's data. -/
def mkR {E : ScBanach} {C U : Set (E.lvl 0)} {r : E.lvl 0 → E.lvl 0}
    (h : IsScRetractionB E C U r) : ScRetraction E C :=
  ⟨U, r, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- The definitional part of B. -/
theorem def_part (E : ScBanach) (C U : Set (E.lvl 0)) (r : E.lvl 0 → E.lvl 0) :
    (∃ R : ScRetraction E C, R.U = U ∧ R.toFun = r) ↔ IsScRetractionB E C U r := by
  constructor
  · rintro ⟨R, rfl, rfl⟩
    exact ⟨R.relOpen, R.mapsTo, R.isScSmooth, R.idem⟩
  · intro h
    exact ⟨mkR h, rfl, rfl⟩

/-- `Dr(r(x)) ∘ Dr(x) = Dr(x)` for `x ∈ U₁` (chain rule), via `Tr ∘ Tr = Tr` on `TU`. -/
theorem chain_part {E : ScBanach} {C U : Set (E.lvl 0)} {r : E.lvl 0 → E.lvl 0}
    (h : IsScRetractionB E C U r) (x₁ y₁ : E.lvl 1) (hx : E.toBase 1 x₁ ∈ U)
    (hy : E.toBase 1 y₁ = r (E.toBase 1 x₁)) :
    (scDeriv U r y₁).comp (scDeriv U r x₁) = scDeriv U r x₁ := by
  ext k
  have hp : ((x₁, k) : E.tangent 0) ∈ E.tangentSet (mkR h).U := hx
  have := congrArg Prod.snd ((mkR h).tangentMap_tangentMap hp)
  change scDeriv U r (levelMap r 1 x₁) (scDeriv U r x₁ k) = scDeriv U r x₁ k at this
  rw [levelMap_eq_of_toBase_eq hy] at this
  exact this

theorem A_to_B : A → B := by
  intro hA
  refine ⟨def_part, fun E C U r h => ⟨chain_part h, ?_⟩⟩
  intro x₁ hx
  exact hA.2.2.2 (mkR h) (x := x₁) hx

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E C R x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨R.mapsTo hy, R.idem y hy⟩
    · rintro ⟨hx, hRx⟩
      exact ⟨x, hx, hRx⟩
  · intro E C R x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact R.idem y hy
  · intro E C R m x hx
    obtain ⟨y, hy, hyx⟩ := hx
    change E.toBase m x ∈ R.U
    rw [← hyx]
    exact R.mapsTo hy
  · intro E C R x hx
    have hR : IsScRetractionB E C R.U R.toFun := ⟨R.relOpen, R.mapsTo, R.isScSmooth, R.idem⟩
    exact (hB.2 E C R.U R.toFun hR).2 x hx

#rt_check RoundTrip.V2_1.A_to_B [Polyfold.ScRetraction.mem_retract_iff,
  Polyfold.ScRetraction.apply_eq_self_of_mem_retract, Polyfold.ScRetraction.lvlSet_retract_subset,
  Polyfold.ScRetraction.scDeriv_comp_self]
#rt_check RoundTrip.V2_1.B_to_A [Polyfold.ScRetraction.mem_retract_iff,
  Polyfold.ScRetraction.apply_eq_self_of_mem_retract, Polyfold.ScRetraction.lvlSet_retract_subset,
  Polyfold.ScRetraction.scDeriv_comp_self]
#rt_overlap RoundTrip.V2_1.B_to_A [Polyfold.ScRetraction.mem_retract_iff,
  Polyfold.ScRetraction.apply_eq_self_of_mem_retract, Polyfold.ScRetraction.lvlSet_retract_subset,
  Polyfold.ScRetraction.scDeriv_comp_self]

end RoundTrip.V2_1
