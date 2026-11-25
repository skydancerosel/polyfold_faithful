import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_114

set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000

/-! Round trip for V17_114 (2021 Theorem 17.6.8, p. 823: under (LUC) the effective integral
`∮_{Θ̂_Ψ} [ω_Ψ]` does not depend on the covering family).

The item lists the definitions `integralEffVia`, `integralEff` (vocabulary) and five theorems;
`A` is the conjunction of their types, at universe `0` (`B` lives on `GCT.{0}`; the half-plane
example has no universe parameter).  Conjuncts: `isLUC_model` ((LUC) for `C` gives (LUC) on every
model), **`theorem_17_6_8`** (the main conjunct: the effective integral on two covering families
agrees when `Θ̂` is tame oriented on both), `theorem_17_6_8_book` (the same with the hypothesis on
the first family only), `halfPlane_isLUC` (the half-plane polyfold has (LUC)),
`halfPlaneArc_stokes_eff` (effective Stokes for the closed half-circle).

* `A_to_B`: `B` is `theorem_17_6_8` at universe `0`.
* `B_to_A`: `theorem_17_6_8` is `B`; `theorem_17_6_8_book` from `B` (the tameness on the second
  family is the `isTameOrientedVia_of_family` term in its statement).  The other three conjuncts do
  not follow from `B` (they are facts of the setting or of one example, not about independence of
  the family); they are re-proved outright: `isLUC_model` and `halfPlane_isLUC` by the project's
  one-line proofs (`isGenIsoInvariant_isLUC`, `arc_isLUC`, `isEquivalence_halfPlaneModelFunctor`),
  `halfPlaneArc_stokes_eff` as an instance of `stokes_eff_dim1_on_C` (effective Stokes for `n = 1`
  on the family chosen by `IsTameOriented`, from the ep-level `EP.stokesWithoutPartitions_all`
  and `isLUC_model'`).

**Harness notes.**  (1) `integralEffVia` (in `B` and in `theorem_17_6_8`) is defined with the
banned `isLUC_model`, abstracted as `integralEffVia._proof_1`; so plain `#rt_check` reports
`isLUC_model` on every statement mentioning it, `B` included, and the checks use
`#rt_check_soft`.  (2) The statement of `halfPlaneArc_stokes_eff` contains the proof term
`halfPlane_isLUC` (a banned theorem of the item) as an argument of `integralEff`; `A`'s body
mentions it directly, not through a `_proof_N` field, so every term mentioning `A` reaches it and
`#rt_check_soft` reports it on `A_to_B` and `B_to_A` (recorded with `#guard_msgs`).  The proofs
do not use it: `A_to_B` and `B_to_A` are assembled from `main_A_to_B`, `main_B_to_A`, `book_of_B`,
`isLUC_model'`, `halfPlane_isLUC'`, `stokes_eff_dim1_on_C` (stated without `A` and without
`halfPlane_isLUC`), which pass `#rt_check` / `#rt_check_soft`. -/

namespace RoundTrip.V17_114
open Polyfold
open Polyfold.GCT.PolyfoldConstruction Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory
open Polyfold.EPLocalization Polyfold.EPLocalization.EPLoc CategoryTheory Polyfold.HalfCircle
open Polyfold.EpGroupoid Polyfold.MPolyfold

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isLUC_model.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8_book.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.halfPlane_isLUC) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_stokes_eff)

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isLUC_model.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8.{0},
    @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8_book.{0},
    @Polyfold.GCT.PolyfoldConstruction.halfPlane_isLUC,
    @Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_stokes_eff⟩

/-! ### The main conjunct `theorem_17_6_8` against `B` -/

theorem main_A_to_B
    (h : type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8.{0}) :
    B := by
  intro C S hL A n hn hc c c' ht ht' ω
  exact h A hL c c' hn hc ht ht' ω

theorem main_B_to_A (hB : B) :
    type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8.{0} := by
  intro C S n A hL c c' hn hc ht ht' ω
  exact hB C S hL A n hn hc c c' ht ht' ω

/-! ### The other conjuncts -/

theorem book_of_B (hB : B) :
    type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8_book.{0} := by
  intro C S n A hL c c' hn hc ht ω
  exact hB C S hL A n hn hc c c' ht _ ω

/-- `isLUC_model`, re-proved (the project's proof). -/
theorem isLUC_model' :
    type_of% @Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isLUC_model.{0} :=
  fun hL c => hL.forall isGenIsoInvariant_isLUC c

/-- `halfPlane_isLUC`, re-proved (the project's proof). -/
theorem halfPlane_isLUC' : halfPlaneConstruction.IsLUC := by
  have : IsIso (localizationFunctor.map (X := AA)
      (Y := halfPlaneConstruction.modelEP halfPlaneFamily.Ψ) halfPlaneModelFunctor) :=
    isInvertedBy_localizationFunctor _ isEquivalence_halfPlaneModelFunctor
  exact ⟨halfPlaneFamily,
    (isGenIsoInvariant_isLUC ((isGeneralizedIso_iff_isIso _).2 this)).1 arc_isLUC⟩

/-- Effective Stokes (`n = 1`) for the integrals on `C`, on the family chosen by
`IsTameOriented`, from the ep-level Stokes theorem `EP.stokesWithoutPartitions_all` (not an item
theorem) and the re-proved `isLUC_model'`.  It does not use `B`. -/
theorem stokes_eff_dim1_on_C {C : GCT.{0}} {S : C.PolyfoldConstruction}
    (A : S.OrientedSubcategory) (hL : S.IsLUC) (hcpt : C.IsCompactBranched A.Θ)
    (h : A.IsTameOriented (0 + 1)) (ω : S.catFormsInfty 0) :
    A.integralEff hL (Nat.succ_pos 0) hcpt h (S.catFormsInftyD 0 ω) =
      A.boundaryIntegralEffDim1 hL hcpt h ω :=
  (S.modelEP h.choose.Ψ).stokesWithoutPartitions_all.stokesEffDim1
    (A.toOriented h.choose).isBranchedEpSubgroupoid (A.isCompactBranched_toOriented hcpt h.choose)
    (A.toOriented h.choose).isOrientation
    ((S.modelEP h.choose.Ψ).hloc_hasLUC_dim1 (isLUC_model' hL h.choose) h.choose_spec)
    (ω.1 h.choose)

theorem A_to_B : A → B := fun h => main_A_to_B h.2.1

theorem B_to_A : B → A := fun hB =>
  ⟨isLUC_model', main_B_to_A hB, book_of_B hB, halfPlane_isLUC',
    stokes_eff_dim1_on_C _ _ _ _⟩

#rt_check_soft RoundTrip.V17_114.main_A_to_B
  [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isLUC_model,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8_book,
   Polyfold.GCT.PolyfoldConstruction.halfPlane_isLUC,
   Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_stokes_eff]
#rt_check_soft RoundTrip.V17_114.main_B_to_A
  [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isLUC_model,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8_book,
   Polyfold.GCT.PolyfoldConstruction.halfPlane_isLUC,
   Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_stokes_eff]
#rt_check_soft RoundTrip.V17_114.book_of_B
  [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isLUC_model,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8_book,
   Polyfold.GCT.PolyfoldConstruction.halfPlane_isLUC,
   Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_stokes_eff]
#rt_check RoundTrip.V17_114.isLUC_model'
  [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isLUC_model,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8_book,
   Polyfold.GCT.PolyfoldConstruction.halfPlane_isLUC,
   Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_stokes_eff]
#rt_check RoundTrip.V17_114.halfPlane_isLUC'
  [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isLUC_model,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8_book,
   Polyfold.GCT.PolyfoldConstruction.halfPlane_isLUC,
   Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_stokes_eff]
#rt_check_soft RoundTrip.V17_114.stokes_eff_dim1_on_C
  [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isLUC_model,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8_book,
   Polyfold.GCT.PolyfoldConstruction.halfPlane_isLUC,
   Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_stokes_eff]

/--
error: rt_check_soft FAIL: RoundTrip.V17_114.A_to_B uses [Polyfold.GCT.PolyfoldConstruction.halfPlane_isLUC]
-/
#guard_msgs (whitespace := lax) in
#rt_check_soft RoundTrip.V17_114.A_to_B
  [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isLUC_model,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8_book,
   Polyfold.GCT.PolyfoldConstruction.halfPlane_isLUC,
   Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_stokes_eff]
/--
error: rt_check_soft FAIL: RoundTrip.V17_114.B_to_A uses [Polyfold.GCT.PolyfoldConstruction.halfPlane_isLUC]
-/
#guard_msgs (whitespace := lax) in
#rt_check_soft RoundTrip.V17_114.B_to_A
  [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isLUC_model,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8_book,
   Polyfold.GCT.PolyfoldConstruction.halfPlane_isLUC,
   Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_stokes_eff]
#rt_overlap RoundTrip.V17_114.B_to_A
  [Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.isLUC_model,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8,
   Polyfold.GCT.PolyfoldConstruction.OrientedSubcategory.theorem_17_6_8_book,
   Polyfold.GCT.PolyfoldConstruction.halfPlane_isLUC,
   Polyfold.GCT.PolyfoldConstruction.halfPlaneArc_stokes_eff]

end RoundTrip.V17_114
