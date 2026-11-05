import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_36

/-!
Round trip for V4_36 (Proposition 4.15 (4)).  `A` is the type of
`Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_15_4`, universe instantiated at `0`:
for every junk value `x₀ : A¹`, every point of `A` is smooth for the induced structure and
`toLevelOne x₀ : A → A¹` is sc-smooth.

Glue:
* B's `IsSmoothSubmanifoldB` is the project's `IsSmoothSubmanifold` (`smooth_iff`, V4_33).
* `A → B`: B's first conjunct `A = A_1` (for the induced structure) cannot be read off `A`, whose
  conclusions need a base point `x₀ ∈ A_1` to be stated; it is the non-banned vocabulary lemma
  `mem_levelSet_subPolyfold_iff` with `mem_levelSet_one`.  B's second conjunct is `A`'s.
* `B → A`: `A`'s first conjunct (`A = A_∞` for the induced structure) is derived from B: an
  sc-smooth map preserves levels (`IsScSmoothMap.mapsTo_levelSet`), and level `m` of `A¹` lies
  over level `m + 1` of `A` (`levelVal_mem_of_shift`, proved here in the level charts), so
  `A_1 = A` and `1₀¹` sc-smooth give `A_m = A` for all `m` by induction.
-/

namespace RoundTrip.V4_36
open Polyfold

def A : Prop := type_of% @Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_15_4.{0}

theorem A_holds : A := @Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_15_4.{0}

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

/-- Definition 4.13: the project's notion is B's (V4_29/V4_33). -/
theorem smooth_iff (P : MPolyfold X) (S : Set X) :
    P.IsSmoothSubmanifold S ↔ IsSmoothSubmanifoldB P S := by
  constructor
  · intro h a ha
    obtain ⟨V, hV, haV, s, hs, himg⟩ := h a ha
    exact ⟨V, s, hV, haV, (retractionOn_iff P s V).1 hs, himg⟩
  · intro h a ha
    obtain ⟨V, s, hV, haV, hs, himg⟩ := h a ha
    exact ⟨V, hV, haV, s, (retractionOn_iff P s V).2 hs, himg⟩

end Glue

/-- Level `m` of `Y¹` lies over level `m + 1` of `Y` (read in the level charts). -/
theorem levelVal_mem_of_shift {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    (Q : MPolyfold Y) [ParacompactSpace (Q.Level 1)] (y : Q.Level 1) (m : ℕ)
    (h : y ∈ Q.shift.levelSet m) : Q.levelVal 1 y ∈ Q.levelSet (m + 1) := by
  obtain ⟨φ, hφ, hyφ⟩ := Q.exists_isChart_mem_source (Q.levelVal 1 y)
  have hsrc : y ∈ (MPolyfold.levelChart hφ y).source := hyφ
  rw [Q.shift.mem_levelSet_iff (Q.shift_isChart hφ y) hsrc] at h
  obtain ⟨w, hw⟩ := h
  rw [Q.mem_levelSet_iff hφ hyφ]
  have hw' : φ.model.E.shift.toBase m w = MPolyfold.levelLift φ 1 (Q.levelVal 1 y) := hw
  refine ⟨(w : φ.model.E (m + 1)), ?_⟩
  rw [ScBanach.shift_toBase φ.model.E m w, hw']
  exact Q.toBase_levelLift hφ hyφ (MPolyfold.levelVal_mem y)

/-- If `Y = Y_1` and `1₀¹ : Y → Y¹` is sc-smooth, every point is smooth. -/
theorem smooth_of_toLevelOne {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    (Q : MPolyfold Y) [ParacompactSpace (Q.Level 1)] (h1 : Q.levelSet 1 = Set.univ)
    (x₀ : Q.Level 1) (hsm : Q.IsScSmoothMap Q.shift (Q.toLevelOne x₀)) (a : Y) :
    a ∈ Q.smoothSet := by
  have ha1 : a ∈ Q.levelSet 1 := h1 ▸ Set.mem_univ a
  have hsucc : ∀ m, a ∈ Q.levelSet (m + 1) := by
    intro m
    induction m with
    | zero => exact ha1
    | succ m ih =>
      have := levelVal_mem_of_shift Q _ (m + 1) (hsm.mapsTo_levelSet (m + 1) ih)
      rwa [MPolyfold.levelVal_toLevelOne x₀ ha1] at this
  simp only [MPolyfold.smoothSet, Set.mem_iInter]
  intro m
  exact Q.levelSet_succ_subset m (hsucc m)

theorem A_to_B : A → B := by
  intro hA X _ _ _ P S hS hsub _
  have hS' : P.IsSmoothSubmanifold S := (smooth_iff P S).2 hS
  refine ⟨Set.eq_univ_of_forall fun a =>
    (hS'.mem_levelSet_subPolyfold_iff a 1).2 (hS'.mem_levelSet_one a.2), fun a₀ => ?_⟩
  exact (hA hS' a₀).2

theorem B_to_A : B → A := by
  intro hB X _ _ _ P S hS _ x₀
  obtain ⟨h1, hsm⟩ := hB X P S ((smooth_iff P S).1 hS) hS.isSubMPolyfold inferInstance
  exact ⟨smooth_of_toLevelOne _ h1 x₀ (hsm x₀), hsm x₀⟩

#rt_check RoundTrip.V4_36.A_to_B [Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_15_4]
#rt_check RoundTrip.V4_36.B_to_A [Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_15_4]
#rt_overlap RoundTrip.V4_36.B_to_A [Polyfold.MPolyfold.IsSmoothSubmanifold.proposition_4_15_4]

end RoundTrip.V4_36
