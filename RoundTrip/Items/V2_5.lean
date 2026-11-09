import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_5

/-! Round trip for V2_5 (Proposition 2.6: sc-smoothness on a retract is independent of the
retraction).

`A` is the conjunction of the types of `Polyfold.proposition_2_1_13_one`, `proposition_2_1_13_two`,
`proposition_2_1_13_three` and `Polyfold.ScRetraction.comp_comp_eqOn` (none has universe parameters:
`ScBanach` lives in `Type`).

`A → B`: (1) is `proposition_2_1_13_one` both ways; (2) is `proposition_2_1_13_two`, after identifying B's
`Tρ(TU_ρ)` (for an arbitrary retraction `ρ` onto `O`) with `r.tangent` by Proposition 2.4
(`proposition_2_1_11`, not one of the item's theorems); (3) is `proposition_2_1_13_three` with the target
retraction `ρ'`, again after `ρ.tangent = r.tangent`.

`B → A`: `proposition_2_1_13_two`, `_3` are B (2), (3) with `ρ = r` (resp. `ρ' = R'`); for
`proposition_2_1_13_one` (which has no target retract) B is applied with the target retract
`(E'₀, E'₀, E')` (the identity retraction of the whole space), and `f(O) ⊆ E'₀` is trivial.
`comp_comp_eqOn` is an elementary identity proved directly. -/

namespace RoundTrip.V2_5
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.proposition_2_1_13_one) ∧ (type_of% @Polyfold.proposition_2_1_13_two) ∧
    (type_of% @Polyfold.proposition_2_1_13_three) ∧ (type_of% @Polyfold.ScRetraction.comp_comp_eqOn)

theorem A_holds : A :=
  ⟨@Polyfold.proposition_2_1_13_one, @Polyfold.proposition_2_1_13_two, @Polyfold.proposition_2_1_13_three,
    @Polyfold.ScRetraction.comp_comp_eqOn⟩

/-- `Tρ(TU_ρ)`, as B writes it, is `ρ.tangent`. -/
theorem image_eq_tangent {E : ScBanach} {C : Set (E.lvl 0)} (ρ : ScRetraction E C) :
    Polyfold.tangentMap ρ.U ρ.toFun '' E.tangentSet ρ.U = ρ.tangent := rfl

theorem A_to_B : A → B := by
  intro hA E E' C O C' O' f _ hfO r s hr hs
  obtain ⟨h1, h2, h3, -⟩ := hA
  refine ⟨⟨fun h => h1 r s (hr.trans hs.symm) h, fun h => h1 s r (hs.trans hr.symm) h⟩,
    fun hf => ⟨?_, ?_⟩⟩
  · intro ρ hρ p hp
    rw [image_eq_tangent, proposition_2_1_11 ρ r (hρ.trans hr.symm)] at hp
    exact h2 r s (hr.trans hs.symm) hf hp
  · intro ρ hρ ρ' hρ'
    rw [image_eq_tangent, image_eq_tangent, proposition_2_1_11 ρ r (hρ.trans hr.symm)]
    exact h3 r ρ' hf (by rw [hr, hρ']; exact hfO)

/-- The whole space `E₀` as a retract (identity retraction). -/
def univRetraction (E : ScBanach) : ScRetraction E univ :=
  ScRetraction.id (U := univ) ⟨isPartialQuadrant_univ E, univ, isOpen_univ, (inter_univ _).symm⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E E' C f R S hRS hf
    have := hB E E' C R.retract univ (univRetraction E').retract f
      (univRetraction E').isScRetract (fun _ _ => by
        change _ ∈ _root_.id '' univ; rw [image_id]; exact mem_univ _) R S rfl hRS.symm
    exact this.1.1 hf
  · intro E E' C f R S hRS hf p hp
    have := hB E E' C R.retract univ (univRetraction E').retract f
      (univRetraction E').isScRetract (fun _ _ => by
        change _ ∈ _root_.id '' univ; rw [image_id]; exact mem_univ _) R S rfl hRS.symm
    exact (this.2 hf).1 R rfl p hp
  · intro E E' C C' f R R' hf hfO
    have := hB E E' C R.retract C' R'.retract f R'.isScRetract hfO R R rfl rfl
    exact (this.2 hf).2 R rfl R' rfl
  · intro E E' C f R S h y hy
    simp only [Function.comp_apply, S.comp_eq_self_of_retract_subset R h hy]

#rt_check RoundTrip.V2_5.A_to_B [Polyfold.proposition_2_1_13_one, Polyfold.proposition_2_1_13_two,
  Polyfold.proposition_2_1_13_three, Polyfold.ScRetraction.comp_comp_eqOn]
#rt_check RoundTrip.V2_5.B_to_A [Polyfold.proposition_2_1_13_one, Polyfold.proposition_2_1_13_two,
  Polyfold.proposition_2_1_13_three, Polyfold.ScRetraction.comp_comp_eqOn]
#rt_overlap RoundTrip.V2_5.B_to_A [Polyfold.proposition_2_1_13_one, Polyfold.proposition_2_1_13_two,
  Polyfold.proposition_2_1_13_three, Polyfold.ScRetraction.comp_comp_eqOn]

end RoundTrip.V2_5
