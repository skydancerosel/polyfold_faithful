import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_81

/-!
Round trip for V3_81 (Theorem 3.54 (1) at the nearby zeros: the kernel).  `A` is the conjunction of
the types of `Polyfold.theorem_3_54_nearby_kernel` (universes `0, 0`),
`Polyfold.theorem_3_54_chart_kernel`, `Polyfold.StabilityData.graphSpace_eq_ker_Dfs'`,
`Polyfold.IsStrongBundleIso.scDeriv_pushforward_at`,
`Polyfold.IsStrongBundleIso.ker_scDeriv_eq_map`, `Polyfold.scDeriv_mem_partialQuadrantAtWith_iff`,
`Polyfold.IsInGoodPosition.isInGoodPositionIn_of_le` and (new in the refresh 2026-11-02)
`Polyfold.IsStrongBundleIso.ker_deriv_eq_map_germ`.  Since the germ reading,
`theorem_3_54_nearby_kernel` assumes the text's germ reading (`IsGoodPositionGermTame`) and states
the kernel of the derivative family `Q` of the filling germ at the level-`1` point `z₀₁`.

Neither direction is proved.  Diagnosis of `A → B` (believed true; proof effort only):
* `A`'s kernel statement (`theorem_3_54_nearby_kernel`, last conjunct) is made in **one** chart:
  the tame chart `c` centred at `x₀` that the theorem constructs, for **one** presentation `T` of
  the quadrant, for the kernel of the filling germ's derivative `Q(z₀₁)` (shown to lie in
  `T_{z₀}O`), with an **algebraic** good complement.  `B` asks for the kernel
  `ker D(f̂ ∘ r)(z₁) ∩ T_zO` in **every** tame strong bundle chart around `y`, for **every**
  presentation of `C`, with an **sc**-complement and no `d_X(y) ≥ 1` case distinction.
* The audit's non-glue obstacle — the smoothness of `ker f'(y)` at the nearby zeros — is gone at
  HEAD: `StrongBundle.linAt_isScFredholm` (non-banned, `#rt_check` against `A`'s list passes)
  makes `f'(y) = Lin(z) : T_zO → K_z` an sc-Fredholm operator in **every** chart around a zero, so
  its kernel is smooth (`IsRegularizing.ker_le_smooth`) and `T_zO` is an sc-subspace.
* What remains is glue, but heavy: `ker Q(z₀₁) = ker Lin(z₀₁)` on `T_{z₀}O` (`linAt_eq_germDeriv`,
  `f̂ = g` on `O` near `φ(y)`); the chart and presentation change to an arbitrary tame chart
  (`StrongBundle.linAt_chart_independence`); the sc-complement inside `T_zO` at the non-central
  point `z` (Proposition 2.35 at `z`, the transport lemma to `E` with the re-centred presentation
  of `C_z` from `Chapter4/Recentre.lean`, `IsInGoodPosition.isInGoodPositionScIn`), with the
  smooth finite-dimensional kernel from `linAt_isScFredholm`.  A few hundred lines through the
  slow destructuring of `theorem_3_54_nearby_kernel`; not attempted within the budget.  All these
  tools pass `#rt_check` (`glue_avail`).  (`theorem_3_54_one'` cannot be borrowed: it uses five
  of `A`'s lemmas.)

`B → A` fails for a real reason: `theorem_3_54_nearby_kernel` assumes only `IsSection` and good
position with an algebraic complement (no tame strong bundle, no sc-Fredholm property), and it
asserts the whole graph description (`σ`, `Yc`, `V'`, the Fredholm index, the chart identities),
none of which `B` states; the other seven conjuncts are chart-level lemmas.
-/
namespace RoundTrip.V3_81
open Polyfold

/-- The project's statement: Theorem 3.54 (1) at the nearby zeros, the kernel (in the chart at
`x₀` and in the abstract chart data), and the six lemmas of its proof (germ reading). -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_54_nearby_kernel.{0, 0} ∧
    type_of% @Polyfold.theorem_3_54_chart_kernel ∧
    type_of% @Polyfold.StabilityData.graphSpace_eq_ker_Dfs' ∧
    type_of% @Polyfold.IsStrongBundleIso.scDeriv_pushforward_at ∧
    type_of% @Polyfold.IsStrongBundleIso.ker_scDeriv_eq_map ∧
    type_of% @Polyfold.scDeriv_mem_partialQuadrantAtWith_iff ∧
    type_of% @Polyfold.IsInGoodPosition.isInGoodPositionIn_of_le ∧
    type_of% @Polyfold.IsStrongBundleIso.ker_deriv_eq_map_germ

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_54_nearby_kernel.{0, 0}, @Polyfold.theorem_3_54_chart_kernel,
    @Polyfold.StabilityData.graphSpace_eq_ker_Dfs', @Polyfold.IsStrongBundleIso.scDeriv_pushforward_at,
    @Polyfold.IsStrongBundleIso.ker_scDeriv_eq_map, @Polyfold.scDeriv_mem_partialQuadrantAtWith_iff,
    @Polyfold.IsInGoodPosition.isInGoodPositionIn_of_le,
    @Polyfold.IsStrongBundleIso.ker_deriv_eq_map_germ⟩

/-- **Diagnostic**: the tools of the remaining glue avoid `A`'s theorems: the sc-Fredholm
linearization in every chart around a zero (`StrongBundle.linAt_isScFredholm`, smooth kernel,
`T_zO` an sc-subspace), the chart and presentation independence of the good position of
`ker Lin(z)` (`StrongBundle.linAt_chart_independence`), and `Lin(z) = Dg(z)` on `T_zO` for a
filling germ (`linAt_eq_germDeriv`). -/
theorem glue_avail : (type_of% @Polyfold.StrongBundle.linAt_isScFredholm.{0, 0}) ∧
    (type_of% @Polyfold.StrongBundle.linAt_chart_independence.{0, 0}) ∧
    (type_of% @Polyfold.linAt_eq_germDeriv) :=
  ⟨@Polyfold.StrongBundle.linAt_isScFredholm.{0, 0},
    @Polyfold.StrongBundle.linAt_chart_independence.{0, 0}, @Polyfold.linAt_eq_germDeriv⟩

#rt_check RoundTrip.V3_81.glue_avail [Polyfold.theorem_3_54_nearby_kernel,
  Polyfold.theorem_3_54_chart_kernel, Polyfold.StabilityData.graphSpace_eq_ker_Dfs',
  Polyfold.IsStrongBundleIso.scDeriv_pushforward_at, Polyfold.IsStrongBundleIso.ker_scDeriv_eq_map,
  Polyfold.scDeriv_mem_partialQuadrantAtWith_iff, Polyfold.IsInGoodPosition.isInGoodPositionIn_of_le,
  Polyfold.IsStrongBundleIso.ker_deriv_eq_map_germ]

end RoundTrip.V3_81
