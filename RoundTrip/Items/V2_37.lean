import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_37

/-! Round trip for V2_37 (Theorem 2.31, first statement: `dim(T_xO/T^R_xO) ≤ d_O(x)`).

`A` is the conjunction of the types of `Polyfold.theorem_2_4_12` (M-polyfold form, universe `0`),
`Polyfold.theorem_2_4_12_retract` (the text's form for a retract `O` viewed as an M-polyfold),
`Polyfold.ScRetraction.IsDiffeoGerm.quotDim_le` (one germ of sc-diffeomorphisms between retracts),
`Polyfold.MPolyfold.quotDim_le_chartDegIndex` (universe `0`), `Polyfold.ScRetraction.scDeriv_restrict`,
`Polyfold.degIndexWith_le_of_germ` and (refresh 2026-11-02, added to the row)
`Polyfold.remark_2_4_8_isPartialQuadrant` (at smooth `x ∈ O`, `C_xO` is a partial quadrant in
`T_xO`, the project's refutation of Remark 2.28's negative claim, via Flor's theorem).

`A → B`: `theorem_2_4_12_retract` at the level-1 point `x₁` (B's smooth `x` lies in `O₁`), with
`reducedTangentSpaceWith R T x₁ = T_xO ⊓ E_x` and `quotDim A (A ⊓ B) = quotDim A B`.

`B → A` fails for a genuine reason: every statement of `A` is for points `x ∈ O₁` (level 1),
while the text (and B) only treat smooth points `x ∈ O_∞`; B says nothing at a point of
`O₁ \ O_∞`.  Restricted to smooth points, `theorem_2_4_12_retract` does follow from B
(`B_to_retract_smooth`).  The other conjuncts of `A` (the M-polyfold form with `d_X`, the germ forms
with `d_{C'}(F(x))`, the derivative of a restricted retraction) are more general statements used in
the project's proof; they are not derivable from B without re-proving the invariance argument.
The new conjunct `remark_2_4_8_isPartialQuadrant` is a different statement (the structure of the
partial cone `C_xO`, Flor's theorem on nonnegative idempotent matrices) that B (a dimension
inequality) does not touch. -/

namespace RoundTrip.V2_37
open Polyfold Set

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.theorem_2_4_12.{0}) ∧ (type_of% @Polyfold.theorem_2_4_12_retract) ∧
    (type_of% @Polyfold.ScRetraction.IsDiffeoGerm.quotDim_le) ∧
    (type_of% @Polyfold.MPolyfold.quotDim_le_chartDegIndex.{0}) ∧
    (type_of% @Polyfold.ScRetraction.scDeriv_restrict) ∧ (type_of% @Polyfold.degIndexWith_le_of_germ) ∧
    (type_of% @Polyfold.remark_2_4_8_isPartialQuadrant)

theorem A_holds : A :=
  ⟨@Polyfold.theorem_2_4_12.{0}, @Polyfold.theorem_2_4_12_retract,
    @Polyfold.ScRetraction.IsDiffeoGerm.quotDim_le, @Polyfold.MPolyfold.quotDim_le_chartDegIndex.{0},
    @Polyfold.ScRetraction.scDeriv_restrict, @Polyfold.degIndexWith_le_of_germ,
    @Polyfold.remark_2_4_8_isPartialQuadrant⟩

/-- `dim(A / (A ∩ (A ∩ B))) = dim(A / (A ∩ B))`. -/
theorem quotDim_inf_self {V : Type*} [AddCommGroup V] [Module ℝ V] (A B : Submodule ℝ V) :
    quotDim A (A ⊓ B) = quotDim A B := by
  unfold quotDim
  have : (A ⊓ B).comap A.subtype = B.comap A.subtype := by
    ext v
    simp [Submodule.mem_comap]
  rw [this]

theorem A_to_B : A → B := by
  intro hA E C O hO x hx _ x₁ hx₁ R hR n W T hT
  subst hx₁
  have hx' : x₁ ∈ E.lvlSet O 1 := by rw [ScBanach.mem_lvlSet]; exact hx
  have h := hA.2.1 (LocalModel.mk E C O hO) ⟨_, hx⟩ R hR T hT (x := x₁) hx'
  rw [reducedTangentSpaceWith, quotDim_inf_self] at h
  exact h

/-- `B` gives `theorem_2_4_12_retract` at smooth points. -/
theorem B_to_retract_smooth (hB : B) (M : LocalModel) (hO : M.O.Nonempty) (R : ScRetraction M.E M.C)
    (hR : R.retract = M.O) {n : ℕ} {W : ScBanach} (T : ScIso M.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (hT : M.C = T 0 ⁻¹' quadrant n W 0) {x : M.E 1} (hx : x ∈ M.E.lvlSet M.O 1)
    (hs : M.E.toBase 1 x ∈ M.E.smooth) :
    quotDim (LinearMap.range (scDeriv R.U R x : M.E 0 →ₗ[ℝ] M.E 0)) (reducedTangentSpaceWith R T x) ≤
      (M.toMPolyfold hO).degIndex ⟨M.E.toBase 1 x, hx⟩ := by
  cases M with
  | mk E C O hOr =>
    have h := hB E C O hOr (E.toBase 1 x) hx hs x rfl R hR n W T hT
    rw [reducedTangentSpaceWith, quotDim_inf_self]
    exact h

#rt_check RoundTrip.V2_37.A_to_B [Polyfold.theorem_2_4_12, Polyfold.theorem_2_4_12_retract,
  Polyfold.ScRetraction.IsDiffeoGerm.quotDim_le, Polyfold.MPolyfold.quotDim_le_chartDegIndex,
  Polyfold.ScRetraction.scDeriv_restrict, Polyfold.degIndexWith_le_of_germ,
  Polyfold.remark_2_4_8_isPartialQuadrant]
#rt_check RoundTrip.V2_37.B_to_retract_smooth [Polyfold.theorem_2_4_12, Polyfold.theorem_2_4_12_retract,
  Polyfold.ScRetraction.IsDiffeoGerm.quotDim_le, Polyfold.MPolyfold.quotDim_le_chartDegIndex,
  Polyfold.ScRetraction.scDeriv_restrict, Polyfold.degIndexWith_le_of_germ,
  Polyfold.remark_2_4_8_isPartialQuadrant]

end RoundTrip.V2_37
