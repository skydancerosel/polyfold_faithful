import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_44

/-!
Round trip for V4_44 (Definition 4.21).  The item lists only the definitions
`Polyfold.IsGeneralPositionRetractAt`, `Polyfold.MPolyfold.SubmanifoldData.IsGeneralPositionChart`
and `Polyfold.MPolyfold.IsGeneralPositionAt`, so `A = True`; the comparison is B itself (the
project's `IsGeneralPositionAt` is the text's notion read in a chart, B's `IsGeneralPositionAtB`),
proved outright (`B_holds`).

Differences between the two definitions, and the glue:
* B asks `V ⊆ dom φ` for the data of Definition 4.13 and uses `φ(A ∩ V)`; the project allows any
  data with `a ∈ V`, `a ∈ dom φ` and uses the shrunk set `W = V ∩ dom φ ∩ s⁻¹(V ∩ dom φ)`.
  Project ⇒ B: replace `V` by `W` (an sc⁺-retraction restricts to the open `s`-invariant `W`);
  B ⇒ project: when `V ⊆ dom φ`, `W = V`.
* `Disjoint` vs `⊓ = ⊥`; the order of the factors in `T_zO ∩ E_z`: trivial.
Both sides ask for an SC-complement (unlike Definition 4.16, V4_38), so tameness of `X` and the
smoothness hypothesis on `A` are not needed.
-/

namespace RoundTrip.V4_44
open Polyfold

def A : Prop := True

theorem A_holds : A := trivial

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- The project's sc⁺-retractions on open sets are B's (copied from V4_9/V4_33). -/
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

variable {P : MPolyfold X} {S : Set X}

/-- The sc⁺-retraction of Definition 4.13 restricts to the shrunk open set `W` of a chart
(copied from V4_38). -/
theorem isScPlusRetractionOn_shrink (d : P.SubmanifoldData S) (φ : MChart X) :
    P.IsScPlusRetractionOn d.s (d.toSubData.shrink φ) :=
  ⟨d.isScPlusRetractionOn.isScSmoothOn.mono (d.toSubData.isOpen_shrink φ) fun _ hx => hx.1.1,
    d.toSubData.mapsTo_shrink φ, fun x hx => d.isScPlusRetractionOn.idem x hx.1.1,
    fun x hx => d.isScPlusRetractionOn.mem_levelSet x hx.1.1, fun x₀ =>
    (d.isScPlusRetractionOn.isScSmoothOn_one x₀).mono (d.toSubData.isOpen_shrink φ)
      fun _ hx => hx.1.1⟩

end Glue

/-- **Definition 4.21**: the project's notion is B's (no tameness needed). -/
theorem B_holds : B := by
  intro X _ _ _ P S a _ _ ha
  constructor
  · rintro ⟨-, d, φ, n, Wq, T, z, had, hφ, haφ, hT, hz, N, M, B', hN, hM, hB'le, hB'sc, hsplit⟩
    refine ⟨d.toSubData.shrink φ, d.s, φ, n, Wq, T, z, N, M,
      (retractionOn_iff P d.s _).1 (isScPlusRetractionOn_shrink d φ), ?_,
      d.toSubData.mem_shrink φ ha had haφ, hφ, d.toSubData.shrink_subset_source φ, hT, hz, ?_, hM,
      B', hB'sc, hB'le, fun m => ⟨(hsplit m).1.eq_bot, (hsplit m).2⟩⟩
    · rw [Set.inter_comm]; exact d.toSubData.image_shrink φ
    · rw [Set.inter_comm]; exact hN
  · rintro ⟨V, s, φ, n, Wq, T, z, N, M, hs, himg, haV, hφ, hVφ, hT, hz, hN, hM, B', hB'sc, hB'le,
      hsplit⟩
    let d : P.SubmanifoldData S := ⟨V, s, hs.1, (retractionOn_iff P s V).2 hs, himg⟩
    have hshrink : d.toSubData.shrink φ = V := by
      ext x
      simp only [MPolyfold.SubData.shrink, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · exact fun h => h.1.1
      · intro hx
        exact ⟨⟨hx, hVφ hx⟩, hs.2.2.1 hx, hVφ (hs.2.2.1 hx)⟩
    refine ⟨ha, d, φ, n, Wq, T, z, haV, hφ, hVφ haV, hT, hz, N, M, B', ?_, hM, hB'le, hB'sc,
      fun m => ⟨disjoint_iff.2 (hsplit m).1, (hsplit m).2⟩⟩
    show (N : Set _) = tangentSpace _ _ (φ '' (d.toSubData.shrink φ ∩ S)) z
    rw [hshrink, Set.inter_comm]; exact hN

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := fun _ => trivial

#rt_check RoundTrip.V4_44.A_to_B []
#rt_check RoundTrip.V4_44.B_to_A []
#rt_overlap RoundTrip.V4_44.B_to_A []
#rt_check RoundTrip.V4_44.B_holds []

end RoundTrip.V4_44
