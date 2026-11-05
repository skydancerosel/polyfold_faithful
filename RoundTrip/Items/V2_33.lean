import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_33

/-! Round trip for V2_33 (Remark 2.28: `T^R_xO ⊆ C_xO ⊆ T_xO`; `C_xO` is in general not a partial
quadrant in `T_xO`).

`A` is the conjunction of the types of the theorems of the row (refresh 2026-11-02: all but the
first were added): `reducedTangentSpaceWith_subset_partialConeWith` (`T^R_xO ⊆ C_xO`),
`remark_2_28_isPartialQuadrant` (at every smooth `x ∈ O`, `T_xO`, `T^R_xO` are sc-subspaces and
`C_xO` IS a partial quadrant in `T_xO`), `remark_2_28_partialConeWith` (the same in the shape of
`B2` below), `flor_nonnegRange_simplicial` (Flor's theorem, universe `.{0}`),
`remark_2_28_quotient_simplicial`, `ScRetraction.isScSubspace_reducedTangentSpaceWith`,
`partialConeWith_eq_image_scDeriv`; no other universe parameters.

* B's first conjunct (both inclusions) follows from A (`A_to_B_of_B2`); `C_xO ⊆ T_xO` holds by
  definition.
* B's second conjunct `B2` (there EXIST a retract and a smooth point where `C_xO` is not a partial
  quadrant in `T_xO`, the text's "in general this is not the case" read literally) is refuted by
  A: `A_to_not_B : A → ¬ B` (from `remark_2_28_partialConeWith`, which is the negation of `B2`'s
  inner statement).  So `A → B` is false (`A` holds), and `not_B` holds.
* `B → A` fails now.  The new conjuncts (Flor's theorem on nonnegative idempotent matrices,
  `C_xO = Dr(x)(C_x)`, the simpliciality of `C_xO / T^R_xO`, `T^R_xO` an sc-subspace, `C_xO` a
  partial quadrant) are not in `B` (whose second conjunct says the opposite of the main one), and
  ex falso is not available either: every proof of `¬ B` goes through the project's Flor argument,
  which is now among the banned theorems.  Only the first conjunct is still obtained, directly
  from the definitions without `B` (`B_to_A_old`). -/

namespace RoundTrip.V2_33
open Polyfold Set

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.reducedTangentSpaceWith_subset_partialConeWith) ∧
    (type_of% @Polyfold.remark_2_28_isPartialQuadrant) ∧
    (type_of% @Polyfold.remark_2_28_partialConeWith) ∧
    (type_of% @Polyfold.flor_nonnegRange_simplicial.{0}) ∧
    (type_of% @Polyfold.remark_2_28_quotient_simplicial) ∧
    (type_of% @Polyfold.ScRetraction.isScSubspace_reducedTangentSpaceWith) ∧
    (type_of% @Polyfold.partialConeWith_eq_image_scDeriv)

theorem A_holds : A :=
  ⟨@Polyfold.reducedTangentSpaceWith_subset_partialConeWith,
    @Polyfold.remark_2_28_isPartialQuadrant, @Polyfold.remark_2_28_partialConeWith,
    @Polyfold.flor_nonnegRange_simplicial.{0}, @Polyfold.remark_2_28_quotient_simplicial,
    @Polyfold.ScRetraction.isScSubspace_reducedTangentSpaceWith,
    @Polyfold.partialConeWith_eq_image_scDeriv⟩

/-- B's second conjunct (copied from the blind file): `C_xO` is not always a partial quadrant. -/
def B2 : Prop :=
  ∃ (E : ScBanach) (C O : Set (E.lvl 0)), IsScRetract E C O ∧
    ∃ x ∈ O, x ∈ E.smooth ∧
    ∃ (x₁ : E.lvl 1), E.toBase 1 x₁ = x ∧
    ∃ (R : ScRetraction E C), R.retract = O ∧
    ∃ (n : ℕ) (W : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)),
      C = T.lvl 0 ⁻¹' quadrant n W 0 ∧
      ∃ h : E.IsScSubspace (tangentAt R x₁),
        ¬ IsPartialQuadrant (E.ofSubspace h) {v | Subtype.val v ∈ partialConeWith R T x₁}

/-- A gives B's first conjunct; with B's (doubtful) second conjunct, all of B. -/
theorem A_to_B_of_B2 : A → B2 → B := by
  intro hA hB2
  refine ⟨?_, hB2⟩
  intro E C O _ x _ _ x₁ _ R _ n W T _
  refine ⟨hA.1 R T x₁, ?_⟩
  rintro v ⟨⟨u, hu⟩, -⟩
  exact ⟨u, hu⟩

/-- The old `B → A` (for the first conjunct only): proved directly from the definitions (B is not
used).  The new conjuncts are not derived; there is no `B_to_A`. -/
theorem B_to_A_old : B → type_of% @Polyfold.reducedTangentSpaceWith_subset_partialConeWith := by
  intro _ E n W C R T x
  rintro v ⟨hv1, hv2⟩
  exact ⟨by obtain ⟨u, hu⟩ := hv1; exact ⟨u, hu⟩,
    minimalSubspaceWith_subset_partialQuadrantAtWith T _ hv2⟩

/-- **`A` refutes `B`**: `B2` (`C_xO` is sometimes not a partial quadrant in `T_xO`) contradicts
`A`'s `remark_2_28_partialConeWith`, which proves Remark 2.28's negative claim false
(`Polyfold/Chapter2/PartialConeQuadrant.lean`). -/
theorem A_to_not_B : A → ¬ B := by
  rintro hA ⟨-, E, C, O, -, x, hxO, hxs, x₁, hx₁, R, hRO, n, W, T, hT, h, hnot⟩
  apply hnot
  have hx : x₁ ∈ E.lvlSet R.retract 1 := by
    change E.toBase 1 x₁ ∈ R.retract
    rw [hx₁, hRO]; exact hxO
  have hs : x₁ ∈ E.smoothLvl 1 := by
    change E.toBase 1 x₁ ∈ E.smooth
    rw [hx₁]; exact hxs
  exact hA.2.2.1 hT hx hs h

/-- **`B` is false** (found after the audit): `A_to_not_B` applied to `A_holds`.  The refutation
is the project's own (Flor's theorem, `remark_2_28_partialConeWith`), so this proof necessarily
uses `A`'s theorems and has no `#rt_check` line; `A_to_not_B` is checked instead. -/
theorem not_B : ¬ B := A_to_not_B A_holds

#rt_check RoundTrip.V2_33.A_to_B_of_B2 [Polyfold.reducedTangentSpaceWith_subset_partialConeWith,
  Polyfold.remark_2_28_isPartialQuadrant, Polyfold.remark_2_28_partialConeWith,
  Polyfold.flor_nonnegRange_simplicial, Polyfold.remark_2_28_quotient_simplicial,
  Polyfold.ScRetraction.isScSubspace_reducedTangentSpaceWith,
  Polyfold.partialConeWith_eq_image_scDeriv]
#rt_check RoundTrip.V2_33.A_to_not_B [Polyfold.reducedTangentSpaceWith_subset_partialConeWith,
  Polyfold.remark_2_28_isPartialQuadrant, Polyfold.remark_2_28_partialConeWith,
  Polyfold.flor_nonnegRange_simplicial, Polyfold.remark_2_28_quotient_simplicial,
  Polyfold.ScRetraction.isScSubspace_reducedTangentSpaceWith,
  Polyfold.partialConeWith_eq_image_scDeriv]
#rt_check RoundTrip.V2_33.B_to_A_old [Polyfold.reducedTangentSpaceWith_subset_partialConeWith,
  Polyfold.remark_2_28_isPartialQuadrant, Polyfold.remark_2_28_partialConeWith,
  Polyfold.flor_nonnegRange_simplicial, Polyfold.remark_2_28_quotient_simplicial,
  Polyfold.ScRetraction.isScSubspace_reducedTangentSpaceWith,
  Polyfold.partialConeWith_eq_image_scDeriv]
#rt_overlap RoundTrip.V2_33.B_to_A_old [Polyfold.reducedTangentSpaceWith_subset_partialConeWith,
  Polyfold.remark_2_28_isPartialQuadrant, Polyfold.remark_2_28_partialConeWith,
  Polyfold.flor_nonnegRange_simplicial, Polyfold.remark_2_28_quotient_simplicial,
  Polyfold.ScRetraction.isScSubspace_reducedTangentSpaceWith,
  Polyfold.partialConeWith_eq_image_scDeriv]

end RoundTrip.V2_33
