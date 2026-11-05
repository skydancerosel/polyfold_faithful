import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_32

/-!
Round trip for V4_32 (Remark 4.14: points with `d_X = 0`, and points where `T_aA` is in good
position).  `A` is the conjunction of the types of `Polyfold.isInGoodPosition_univ`,
`Polyfold.partialQuadrantAtWith_eq_univ_of_degIndex_eq_zero` (no universe parameters),
`Polyfold.MPolyfold.isGoodPositionAt_of_degIndex_eq_zero` and
`Polyfold.MPolyfold.hasCornerStructure_of_degIndex_eq_zero` (universe instantiated at `0`).

Neither full direction is proved.
* `A → B` fails on B's second conjunct: A says nothing about points where `T_aA` is in good
  position (with `d_X(a) ≥ 1`); that claim is a local Theorem 4.18 (Proposition 4.9 in a chart
  re-centred at `a`), not contained in A.  B's FIRST conjunct (`d_X(a) = 0`) is proved from A
  (`A_to_B1`): restrict `A` to the open set `W = {d_X < 1}` (`isOpen_setOf_degIndex_lt`, Lemma
  2.23), where `A ∩ W` is again a smooth submanifold, apply A's global
  `hasCornerStructure_of_degIndex_eq_zero` to it, and get `d_{A∩W} ≡ 0` from Lemma 2.26
  (`d_A ≤ d_X`).
* `B → A` fails: A's first two conjuncts are general chart-level facts (every subspace is in good
  position to the whole space; `C_e = E` when `d_C(e) = 0`) and the third is Definition 4.16
  (good position inside `T_aX`) at points with `d_X = 0`, none of which B states; the fourth
  (global corner structure when `d_X ≡ 0` on `A`) would need gluing B's local corner structures on
  the subtypes `A ∩ W_a` into one on `A`.
-/

namespace RoundTrip.V4_32
open Polyfold Set

def A : Prop :=
  type_of% @Polyfold.isInGoodPosition_univ ∧
    type_of% @Polyfold.partialQuadrantAtWith_eq_univ_of_degIndex_eq_zero ∧
    type_of% @Polyfold.MPolyfold.isGoodPositionAt_of_degIndex_eq_zero.{0} ∧
    type_of% @Polyfold.MPolyfold.hasCornerStructure_of_degIndex_eq_zero.{0}

theorem A_holds : A :=
  ⟨@Polyfold.isInGoodPosition_univ, @Polyfold.partialQuadrantAtWith_eq_univ_of_degIndex_eq_zero,
    @Polyfold.MPolyfold.isGoodPositionAt_of_degIndex_eq_zero.{0},
    @Polyfold.MPolyfold.hasCornerStructure_of_degIndex_eq_zero.{0}⟩

/-- B's first conjunct (points with `d_X(a) = 0`), copied verbatim. -/
def B1 : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
    (A : Set X), IsSmoothSubmanifoldB P A → ∀ a ∈ A, P.degIndex a = 0 →
      ∃ W : Set X, IsOpen W ∧ a ∈ W ∧
        ∃ (hW : P.IsSubMPolyfold (A ∩ W)) (_ : ParacompactSpace ↑(A ∩ W)),
          (P.subPolyfold hW).HasCornerStructure ∧ (P.subPolyfold hW).IsWithoutBoundary

example : B → B1 := fun h => h.1

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- The project's sc⁺-retractions on open sets are B's (copied from V4_9). -/
theorem retractionOn_iff (P : MPolyfold X) (r : X → X) (V : Set X) :
    P.IsScPlusRetractionOn r V ↔ IsScPlusRetractionOnB P r V := by
  constructor
  · intro h
    refine ⟨h.isScSmoothOn.isOpen, h.isScSmoothOn, h.mapsTo, h.idem, h.mem_levelSet,
      fun g hg => ?_⟩
    rcases isEmpty_or_nonempty X with hX | ⟨⟨x⟩⟩
    · exact MPolyfold.IsScSmoothOn.of_exists_charts h.isScSmoothOn.isOpen
        (fun y _ => (IsEmpty.false y).elim) (fun y _ => (IsEmpty.false y).elim)
    · refine (h.isScSmoothOn_one (g x)).congr fun y hy => ?_
      change P.toLevelOne (g x) (r y) = g y
      rw [← hg y hy, MPolyfold.toLevelOne_levelVal]
  · rintro ⟨-, h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, fun x₀ =>
      h5 _ fun x hx => MPolyfold.levelVal_toLevelOne x₀ (h4 x hx)⟩

/-- The trace of a smooth finite-dimensional submanifold on an open set is one. -/
theorem smooth_inter_open {P : MPolyfold X} {S W : Set X} (hS : IsSmoothSubmanifoldB P S)
    (hW : IsOpen W) : P.IsSmoothSubmanifold (S ∩ W) := by
  intro a ha
  obtain ⟨V, s, hV, haV, hs, himg⟩ := hS a ha.1
  have hsP := (retractionOn_iff P s V).2 hs
  have hfix : ∀ y ∈ S ∩ V, s y = y := fun y hy => by
    rw [← himg] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hsP.idem x hx
  set V' := (V ∩ W) ∩ s ⁻¹' (V ∩ W) with hV'def
  have hV' : IsOpen V' :=
    (hsP.isScSmoothOn.continuousOn.mono inter_subset_left).isOpen_inter_preimage (hV.inter hW)
      (hV.inter hW)
  have hmaps : MapsTo s V' V' := fun x hx =>
    ⟨hx.2, by rw [mem_preimage, hsP.idem x hx.1.1]; exact hx.2⟩
  have hsub : V' ⊆ V := fun x hx => hx.1.1
  refine ⟨V', hV', ⟨⟨haV, ha.2⟩, by rw [mem_preimage, hfix a ⟨ha.1, haV⟩]; exact ⟨haV, ha.2⟩⟩,
    s, ⟨hsP.isScSmoothOn.mono hV' hsub, hmaps, fun x hx => hsP.idem x (hsub hx),
      fun x hx => hsP.mem_levelSet x (hsub hx), fun x₀ => (hsP.isScSmoothOn_one x₀).mono hV' hsub⟩,
    ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : s x ∈ S ∩ V := himg ▸ mem_image_of_mem s hx.1.1
    exact ⟨⟨h1.1, hx.2.2⟩, hmaps hx⟩
  · rintro ⟨⟨hyS, -⟩, hyV'⟩
    exact ⟨y, hyV', hfix y ⟨hyS, hyV'.1.1⟩⟩

end Glue

/-- A gives B's first conjunct (the `d_X(a) = 0` half of the remark). -/
theorem A_to_B1 : A → B1 := by
  rintro ⟨-, -, -, h4⟩ X _ _ _ P S hS a ha h0
  set W := {x | P.degIndex x < 1} with hWdef
  have hW : IsOpen W := P.isOpen_setOf_degIndex_lt 1
  have hS' : P.IsSmoothSubmanifold (S ∩ W) := smooth_inter_open hS hW
  have : ParacompactSpace ↑(S ∩ W) := P.paracompactSpace_subtype _
  refine ⟨W, hW, (show P.degIndex a < 1 by omega), hS'.isSubMPolyfold, inferInstance,
    h4 hS' fun b hb => Nat.lt_one_iff.1 hb.2, fun x => ?_⟩
  have h1 := lemma_2_26 hS'.isSubMPolyfold x
  have h2 : P.degIndex x.1 < 1 := x.2.2
  omega

#rt_check RoundTrip.V4_32.A_to_B1 [Polyfold.isInGoodPosition_univ,
  Polyfold.partialQuadrantAtWith_eq_univ_of_degIndex_eq_zero,
  Polyfold.MPolyfold.isGoodPositionAt_of_degIndex_eq_zero,
  Polyfold.MPolyfold.hasCornerStructure_of_degIndex_eq_zero]

end RoundTrip.V4_32
