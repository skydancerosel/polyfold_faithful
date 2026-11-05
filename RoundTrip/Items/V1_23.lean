import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_23

/-! Round trip for V1_23 (Theorem 1.25, boundary recognition).

`A` is the conjunction of the types of `Polyfold.theorem_1_25`, `Polyfold.theorem_1_25_lvl1`,
`Polyfold.degIndexWith_le_of_germ`, `Polyfold.eventually_degIndexWith_le`,
`Polyfold.exists_tendsto_lvl1_degIndexWith` and `Polyfold.IsSc1With.mapsTo_minimalSubspace`.
None has universe parameters (`ScBanach` lives in `Type`).

`A → B`: apply `theorem_1_25` to the restricted domains `O ∩ U`, `O' ∩ U'` (again relatively open
in `C`, `C'`), with sc-smooth ⇒ sc¹, and convert the choice-based `degIndex` into `degIndexWith`
for the given presentations by `degIndex_eq` (Lemma 1.24, not part of this item).

`B → A` is not attempted: `theorem_1_25` assumes only that `f` and its inverse are sc¹, while `B`
assumes sc-smooth, and `A` also contains the retract version `degIndexWith_le_of_germ` and
auxiliary lemmas (upper semicontinuity, level-1 approximation, the minimal-subspace property of
`Df(x)`) that `B` does not mention. -/

namespace RoundTrip.V1_23
open Polyfold

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.theorem_1_25) ∧ (type_of% @Polyfold.theorem_1_25_lvl1) ∧
    (type_of% @Polyfold.degIndexWith_le_of_germ) ∧ (type_of% @Polyfold.eventually_degIndexWith_le) ∧
    (type_of% @Polyfold.exists_tendsto_lvl1_degIndexWith) ∧
    (type_of% @Polyfold.IsSc1With.mapsTo_minimalSubspace)

theorem A_holds : A :=
  ⟨@Polyfold.theorem_1_25, @Polyfold.theorem_1_25_lvl1, @Polyfold.degIndexWith_le_of_germ,
    @Polyfold.eventually_degIndexWith_le, @Polyfold.exists_tendsto_lvl1_degIndexWith,
    @Polyfold.IsSc1With.mapsTo_minimalSubspace⟩

/-- Shrinking a relatively open subset of a partial quadrant by an open set. -/
theorem relOpen_inter {E : ScBanach} {C U O : Set (E.lvl 0)} (hU : IsRelOpenInQuadrant E C U)
    (hO : IsOpen O) : IsRelOpenInQuadrant E C (O ∩ U) := by
  refine ⟨hU.isPartialQuadrant, ?_⟩
  obtain ⟨O₁, hO₁, rfl⟩ := hU.relOpen
  exact ⟨O ∩ O₁, hO.inter hO₁, (Set.inter_assoc _ _ _).symm⟩

theorem mem_C {E : ScBanach} {C U O : Set (E.lvl 0)} (hU : IsRelOpenInQuadrant E C U)
    {x : E.lvl 0} (hx : x ∈ O ∩ U) : x ∈ C := by
  obtain ⟨O₁, -, rfl⟩ := hU.relOpen
  exact hx.2.2

theorem A_to_B : A → B := by
  intro hA E E' C U C' U' hU hU' x f g O O' hO hO' hx hfV hgV hgf hfg hf hg n n' W W' T T' hT hT'
  have h := hA.1 (relOpen_inter hU hO) (relOpen_inter hU' hO') ((hf 1).1) ((hg 1).1) hfV hgV
    (fun y hy => hgf hy) (fun y hy => hfg hy) hx
  rw [degIndex_eq T hT (mem_C hU hx), degIndex_eq T' hT' (mem_C hU' (hfV hx))] at h
  exact h

#rt_check RoundTrip.V1_23.A_to_B [Polyfold.theorem_1_25, Polyfold.theorem_1_25_lvl1,
  Polyfold.degIndexWith_le_of_germ, Polyfold.eventually_degIndexWith_le,
  Polyfold.exists_tendsto_lvl1_degIndexWith, Polyfold.IsSc1With.mapsTo_minimalSubspace]

end RoundTrip.V1_23
