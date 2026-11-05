import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_4

/-! Round trip for V2_4 (Definition 2.5: the tangent `T(O, C, E) = (TO, TC, TE)` of a retract;
Definition 2.17: `T_xO = p⁻¹(x) = Dr(x)E`).

`A` is the conjunction of the types of `Polyfold.retractTangent_eq`,
`Polyfold.ScRetraction.mem_tangent_iff_exists`, `Polyfold.ScRetraction.mem_tangent_iff_mem_range`,
`Polyfold.tangentSpace_eq_range` and `Polyfold.tangentSpace_eq_coe_submodule` (no universe
parameters: `ScBanach` lives in `Type`).  `retractTangent` and `tangentSpace` are definitions
(vocabulary).

`A → B`: B's explicit set `TOB R = {(r(x), Dr(x)h)}` (with `r(x)` given as the level-1 point over
`r(ι₁ x₁)`) is `R.tangent` by `mem_tangent_iff_exists` plus `levelMap_eq_of_toBase_eq` /
`IsSc0.toBase_levelMap`; then `retractTangent = TOB R` is `retractTangent_eq`, the `E`/`C`
components of `LocalModel.tangent` are `rfl`, and the fibre claims are `tangentSpace_eq_range`.

`B → A`: `retractTangent_eq` and the fibre statements are read off B (instantiated at the retract
`R.retract`); `mem_tangent_iff_exists` is the definition of the image `Tr(TU)` and is proved
directly; `tangentSpace_eq_coe_submodule` is `tangentSpace_eq_range` (from B) with
`LinearMap.range` coerced. -/

namespace RoundTrip.V2_4
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.retractTangent_eq) ∧
    (type_of% @Polyfold.ScRetraction.mem_tangent_iff_exists) ∧
    (type_of% @Polyfold.ScRetraction.mem_tangent_iff_mem_range) ∧
    (type_of% @Polyfold.tangentSpace_eq_range) ∧
    (type_of% @Polyfold.tangentSpace_eq_coe_submodule)

theorem A_holds : A :=
  ⟨@Polyfold.retractTangent_eq, @Polyfold.ScRetraction.mem_tangent_iff_exists,
    @Polyfold.ScRetraction.mem_tangent_iff_mem_range, @Polyfold.tangentSpace_eq_range,
    @Polyfold.tangentSpace_eq_coe_submodule⟩

/-- `Tr(TU)` is B's explicit set, given the explicit description of `Tr(TU)` by pairs
`(r₁(x), Dr(x)h)`. -/
theorem tangent_eq_TOB {E : ScBanach} {C : Set (E.lvl 0)} (R : ScRetraction E C)
    (hex : ∀ p : E.tangent 0, p ∈ R.tangent ↔
      ∃ x ∈ E.lvlSet R.U 1, ∃ h : E 0, p = (levelMap R 1 x, scDeriv R.U R x h)) :
    R.tangent = TOB R := by
  ext p
  rw [hex p]
  constructor
  · rintro ⟨x, hx, h, rfl⟩
    exact ⟨x, hx, h, R.isSc1.isSc0.toBase_levelMap (m := 1) hx, rfl⟩
  · rintro ⟨x, hx, h, h1, h2⟩
    exact ⟨x, hx, h, Prod.ext (levelMap_eq_of_toBase_eq h1).symm h2⟩

theorem A_to_B : A → B := by
  rintro ⟨hTeq, hex, _, hrange, _⟩ E C O hO
  have hT : ∀ R : ScRetraction E C, R.tangent = TOB R := fun R => tangent_eq_TOB R (fun p => hex R)
  have hrt : ∀ R : ScRetraction E C, R.retract = O → retractTangent E C O = TOB R := by
    rintro R rfl
    rw [hTeq R, hT R]
  refine ⟨fun R hR => ⟨hrt R hR, hT R⟩, ⟨rfl, rfl, fun R hR => hrt R hR⟩, ?_⟩
  intro x₁ hx R hR
  have hfib : tangentSpace E C O x₁ = TxOB R x₁ := by
    ext h
    change ((x₁, h) : E.tangent 0) ∈ retractTangent E C O ↔ ((x₁, h) : E.tangent 0) ∈ TOB R
    rw [hrt R hR]
  refine ⟨hfib, ?_⟩
  rw [← hfib]
  subst hR
  exact hrange R hx

/-- `mem_tangent_iff_exists`, re-proved: `Tr(TU)` is an image. -/
theorem mem_tangent_iff_exists' {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C)
    {p : E.tangent 0} :
    p ∈ R.tangent ↔ ∃ x ∈ E.lvlSet R.U 1, ∃ h : E 0, p = (levelMap R 1 x, scDeriv R.U R x h) := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.1, hq, q.2, rfl⟩
  · rintro ⟨x, hx, h, rfl⟩
    exact ⟨(x, h), hx, rfl⟩

theorem B_to_A : B → A := by
  intro hB
  -- B instantiated at the retract `R.retract`
  have hB' := fun {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C) =>
    hB E C R.retract ⟨R, rfl⟩
  have hTeq : ∀ {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C),
      retractTangent E C R.retract = R.tangent := fun R =>
    ((hB' R).1 R rfl).1.trans ((hB' R).1 R rfl).2.symm
  have hrange : ∀ {E : ScBanach} {C : Set (E 0)} (R : ScRetraction E C) {x : E 1},
      x ∈ E.lvlSet R.retract 1 → tangentSpace E C R.retract x = range (scDeriv R.U R x) :=
    fun R x hx => ((hB' R).2.2 x hx R rfl).1.trans ((hB' R).2.2 x hx R rfl).2
  refine ⟨fun R => hTeq R, fun R p => mem_tangent_iff_exists' R, ?_, fun R x hx => hrange R hx, ?_⟩
  · intro E C R x hx h
    have h1 : h ∈ tangentSpace E C R.retract x ↔ h ∈ range (scDeriv R.U R x) := by
      rw [hrange R hx]
    rw [← h1]
    change _ ↔ ((x, h) : E.tangent 0) ∈ retractTangent E C R.retract
    rw [hTeq R]
  · intro E C R x hx
    rw [hrange R hx]
    ext h
    simp [LinearMap.mem_range]

#rt_check_soft RoundTrip.V2_4.A_to_B [Polyfold.retractTangent_eq,
  Polyfold.ScRetraction.mem_tangent_iff_exists, Polyfold.ScRetraction.mem_tangent_iff_mem_range,
  Polyfold.tangentSpace_eq_range, Polyfold.tangentSpace_eq_coe_submodule]
#rt_check_soft RoundTrip.V2_4.B_to_A [Polyfold.retractTangent_eq,
  Polyfold.ScRetraction.mem_tangent_iff_exists, Polyfold.ScRetraction.mem_tangent_iff_mem_range,
  Polyfold.tangentSpace_eq_range, Polyfold.tangentSpace_eq_coe_submodule]
#rt_overlap RoundTrip.V2_4.B_to_A [Polyfold.retractTangent_eq,
  Polyfold.ScRetraction.mem_tangent_iff_exists, Polyfold.ScRetraction.mem_tangent_iff_mem_range,
  Polyfold.tangentSpace_eq_range, Polyfold.tangentSpace_eq_coe_submodule]

end RoundTrip.V2_4
