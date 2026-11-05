import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_47

/-!
Round trip for V3_47 (Definition 3.53, good position), refreshed 2026-11-02 against HEAD (germ
reading).  `A` is the conjunction of the types of the listed theorems
`Polyfold.StrongBundle.IsGoodPositionGerm.forall_isGoodPositionAtGerm`,
`Polyfold.IsFillingGerm.ker_deriv_le_range`,
`Polyfold.StrongBundle.IsGoodPositionGermTame.isGoodPositionGermSc` and
`Polyfold.StrongBundle.isGoodPositionGermSc_iff` (universes at `0`); `IsGoodPositionAtGerm`,
`IsGoodPositionAt`, `IsInGoodPositionIn`, `StrongBundle.IsGoodPositionGerm`,
`IsScGoodComplementIn`, `IsInGoodPositionScIn`, `IsGoodPositionAtScGerm`, `IsGoodPositionAtSc`,
`StrongBundle.IsGoodPositionGermSc` are definitions (vocabulary).

Neither direction is proved (see the JSON).  `kernel_part` (from `A`) identifies the blind kernel
`ker (Dg(0) ∘ Dr(0)) ∩ T₀O` with the project's `ker Dg(0)`.  The new conjunct
`IsGoodPositionGermTame.isGoodPositionGermSc` supplies the text's sc-complement, but only for a
**tame sc-Fredholm section** (`IsScFredholmSectionTame f`, a global hypothesis); B is an
equivalence of definitions at a zero of an arbitrary map `f : X → Y` in a tame bundle, without
that hypothesis, and its blind side puts the good position in a tame chart different from the
chart of the germ data (chart independence of good position needs a globally sc-smooth section,
`StrongBundle.isGoodPositionAtGerm_of_chart_dense`).
-/

open Set Filter Topology Function

noncomputable section

namespace RoundTrip.V3_47
open Polyfold StrongRetr

/-- The project's statement: the theorems among the decls, universes at `0`. -/
def A : Prop :=
  type_of% @Polyfold.StrongBundle.IsGoodPositionGerm.forall_isGoodPositionAtGerm.{0, 0} ∧
    type_of% @Polyfold.IsFillingGerm.ker_deriv_le_range ∧
    type_of% @Polyfold.StrongBundle.IsGoodPositionGermTame.isGoodPositionGermSc.{0, 0} ∧
    type_of% @Polyfold.StrongBundle.isGoodPositionGermSc_iff.{0, 0}

theorem A_holds : A :=
  ⟨@Polyfold.StrongBundle.IsGoodPositionGerm.forall_isGoodPositionAtGerm.{0, 0},
    @Polyfold.IsFillingGerm.ker_deriv_le_range,
    @Polyfold.StrongBundle.IsGoodPositionGermTame.isGoodPositionGermSc.{0, 0},
    @Polyfold.StrongBundle.isGoodPositionGermSc_iff.{0, 0}⟩

/-- **What `A` contributes to `B`** (proved from the hypothesis `A`, conjunct
`IsFillingGerm.ker_deriv_le_range`): the blind kernel `ker D(0) ∩ T₀O`, with
`D(0) = Dg(0) ∘ Dr(0)` the linearization of `f̂ ∘ r` for a filling germ `g` with derivative family
`Dg`, is the project's kernel `ker Dg(0)`. -/
theorem kernel_part (hA : A) {E F : ScBanach} {C U : Set (E.lvl 0)}
    {R : E.lvl 0 × F.lvl 0 → E.lvl 0 × F.lvl 0} {hU : IsRelOpenInQuadrant E C U}
    {hR : IsStrongBundleRetraction U R} {h0 : (0 : E.lvl 0) ∈ U} {fb g : E.lvl 0 → F.lvl 0}
    (hfg : IsFillingGerm hU hR h0 fb g) {G : ScNbhdGerm E C} (hG : G.U 0 ⊆ U)
    {Dg : E.lvl 1 → E.lvl 0 →L[ℝ] F.lvl 0} (hg : IsSc1GermWith G g Dg) (hg0 : g 0 = 0)
    (h0O : (0 : E.lvl 0) ∈ r R '' U) (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) :
    LinearMap.ker (((Dg 0).comp (scDeriv U (r R) 0) : E.lvl 0 →L[ℝ] F.lvl 0) :
        E.lvl 0 →ₗ[ℝ] F.lvl 0) ⊓
      LinearMap.range (scDeriv U (r R) 0 : E.lvl 0 →ₗ[ℝ] E.lvl 0) =
    LinearMap.ker (Dg 0 : E.lvl 0 →ₗ[ℝ] F.lvl 0) := by
  have hle := hA.2.1 hfg hG hg hg0 h0O hfK
  ext x
  simp only [Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.coe_comp, Function.comp_apply]
  constructor
  · rintro ⟨hx, y, rfl⟩
    rw [ContinuousLinearMap.coe_coe] at hx ⊢
    rwa [scDeriv_r_idem hU hR h0O] at hx
  · intro hx
    obtain ⟨y, hy⟩ := hle (by rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]; exact hx)
    refine ⟨?_, y, hy⟩
    rw [ContinuousLinearMap.coe_coe] at hy
    rw [← hy, scDeriv_r_idem hU hR h0O, hy]
    exact hx

#rt_check RoundTrip.V3_47.kernel_part [Polyfold.StrongBundle.IsGoodPositionGerm.forall_isGoodPositionAtGerm,
  Polyfold.IsFillingGerm.ker_deriv_le_range,
  Polyfold.StrongBundle.IsGoodPositionGermTame.isGoodPositionGermSc,
  Polyfold.StrongBundle.isGoodPositionGermSc_iff]

end RoundTrip.V3_47

end
