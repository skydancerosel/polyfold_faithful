import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_3

/-! Round trip for V2_3 (Proposition 2.4: `Tr(TU) = Tr'(TU')` when `r(U) = r'(U')`).

`A` is the conjunction of the types of `Polyfold.proposition_2_4`,
`Polyfold.ScRetraction.comp_eq_self_of_retract_subset`,
`Polyfold.ScRetraction.tangent_subset_of_retract_subset` and `Polyfold.ScRetraction.mem_tangent_iff`
(no universe parameters: `ScBanach` lives in `Type`).  `ScRetraction.tangent` is a definition
(vocabulary): `R.tangent = tangentMap R.U R '' E.tangentSet R.U` by `rfl`, exactly B's sets.

`A → B`: `proposition_2_4`, unfolding `tangent`.

`B → A`: the main conjunct `proposition_2_4` is B itself.  The three helper conjuncts (the
idempotence identity `r' ∘ r = r`, the fixed-point description `TO = {p ∈ TU | Tr(p) = p}`, and the
inclusion version `r(U) ⊆ r'(U') ⇒ Tr(TU) ⊆ Tr'(TU')`) are proved directly (they are not consequences
of B, which only compares retractions with *equal* images), by the text's own argument (chain rule
`theorem_1_21` applied to `r' ∘ r = r`), avoiding the banned lemmas. -/

namespace RoundTrip.V2_3
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.proposition_2_4) ∧
    (type_of% @Polyfold.ScRetraction.comp_eq_self_of_retract_subset) ∧
    (type_of% @Polyfold.ScRetraction.tangent_subset_of_retract_subset) ∧
    (type_of% @Polyfold.ScRetraction.mem_tangent_iff)

theorem A_holds : A :=
  ⟨@Polyfold.proposition_2_4, @Polyfold.ScRetraction.comp_eq_self_of_retract_subset,
    @Polyfold.ScRetraction.tangent_subset_of_retract_subset, @Polyfold.ScRetraction.mem_tangent_iff⟩

theorem A_to_B : A → B := by
  intro hA E C r r' h
  exact hA.1 r r' h

/-- The fixed-point description of `Tr(TU)`, re-proved (it is a conjunct of `A`). -/
theorem mem_tangent_iff' {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C)
    {p : E.tangent 0} :
    p ∈ R.tangent ↔ p ∈ E.tangentSet R.U ∧ tangentMap R.U R p = p := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨R.tangentMap_mapsTo hq, R.tangentMap_tangentMap hq⟩
  · rintro ⟨hp, hfix⟩
    exact ⟨p, hp, hfix⟩

/-- The base point of an element of `Tr(TU)` lies in `O₁` (re-proved without `mem_tangent_iff`). -/
theorem fst_mem_of_mem_tangent' {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C)
    {p : E.tangent 0} (hp : p ∈ R.tangent) : p.1 ∈ E.lvlSet R.retract 1 := by
  obtain ⟨hpU, hfix⟩ := (mem_tangent_iff' R).1 hp
  have h1 : levelMap R 1 p.1 = p.1 := congrArg Prod.fst hfix
  rw [ScBanach.mem_lvlSet, R.mem_retract_iff]
  refine ⟨hpU, ?_⟩
  have := R.isSc1.isSc0.toBase_levelMap (m := 1) hpU
  rw [h1] at this
  exact this.symm

/-- The inclusion version `r(U) ⊆ r'(U') ⇒ Tr(TU) ⊆ Tr'(TU')` (re-proved: the chain rule for
`r' ∘ r = r`). -/
theorem tangent_subset' {E : ScBanach} {C : Set (E 0)} (R R' : ScRetraction E C)
    (h : R.retract ⊆ R'.retract) : R.tangent ⊆ R'.tangent := by
  intro p hp
  obtain ⟨hpU, hfix⟩ := (mem_tangent_iff' R).1 hp
  have hpU' : p ∈ E.tangentSet R'.U :=
    E.lvlSet_mono R'.retract_subset 1 (E.lvlSet_mono h 1 (fst_mem_of_mem_tangent' R hp))
  rw [mem_tangent_iff' R']
  refine ⟨hpU', ?_⟩
  have hmaps : MapsTo R R.U R'.U := fun y hy => R'.retract_subset (h (R.apply_mem_retract hy))
  obtain ⟨_, hchain⟩ := theorem_1_21 R.relOpen R'.relOpen R.isSc1 R'.isSc1 hmaps
  have hcongr : EqOn (tangentMap R.U (R' ∘ R)) (tangentMap R.U R) (E.tangentSet R.U) :=
    (R.isSc1.tangentMap_congr R.isScDomain fun y hy =>
      (R'.apply_eq_self_of_mem_retract (h (R.apply_mem_retract hy))).symm).symm
  have := (hchain hpU).symm.trans (hcongr hpU)
  change tangentMap R'.U R' (tangentMap R.U R p) = tangentMap R.U R p at this
  rwa [hfix] at this

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {E} {C} R R' h => hB E C R R' h, ?_, ?_, ?_⟩
  · intro E C R R' h y hy
    exact R'.apply_eq_self_of_mem_retract (h (R.apply_mem_retract hy))
  · intro E C R R' h
    exact tangent_subset' R R' h
  · intro E C R p
    exact mem_tangent_iff' R

#rt_check RoundTrip.V2_3.A_to_B [Polyfold.proposition_2_4,
  Polyfold.ScRetraction.comp_eq_self_of_retract_subset,
  Polyfold.ScRetraction.tangent_subset_of_retract_subset, Polyfold.ScRetraction.mem_tangent_iff]
#rt_check RoundTrip.V2_3.B_to_A [Polyfold.proposition_2_4,
  Polyfold.ScRetraction.comp_eq_self_of_retract_subset,
  Polyfold.ScRetraction.tangent_subset_of_retract_subset, Polyfold.ScRetraction.mem_tangent_iff]
#rt_overlap RoundTrip.V2_3.B_to_A [Polyfold.proposition_2_4,
  Polyfold.ScRetraction.comp_eq_self_of_retract_subset,
  Polyfold.ScRetraction.tangent_subset_of_retract_subset, Polyfold.ScRetraction.mem_tangent_iff]

end RoundTrip.V2_3
