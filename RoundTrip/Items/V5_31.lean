import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_31

namespace RoundTrip.V5_31
open Polyfold

/-- The project's statement: the only theorem among the decls is
`IsGeneralPositionGerm.isLinSurjAt` (general position contains the surjectivity), universes
instantiated at `0`; `IsGeneralPositionGerm` and `linKer` are vocabulary. -/
def A : Prop := type_of% @Polyfold.StrongBundle.IsGeneralPositionGerm.isLinSurjAt.{0, 0}

theorem A_holds : A := @Polyfold.StrongBundle.IsGeneralPositionGerm.isLinSurjAt.{0, 0}

set_option linter.unusedSectionVars false

section Glue
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The project's `linKer` (kernel of `linAt`, pushed into `E₀`) is B's `kerLin = T_zO ∩ ker Dg`. -/
theorem linKer_eq (c : StrongBundleChart PX P) (f : X → Y) (z : c.φ.model.E 1) :
    c.linKer f z = kerLin c f z := by
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.2, hu⟩
  · rintro ⟨hv, hv0⟩
    exact ⟨⟨v, hv⟩, hv0, rfl⟩

/-- The project's reduced tangent space of the base retraction is B's `T_zO ∩ E_{φ(x)}`. -/
theorem reduced_eq (c : StrongBundleChart PX P) (z : c.φ.model.E 1) {x : X}
    (hz : c.φ.model.E.toBase 1 z = c.φ x) {n : ℕ} {W : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)) :
    reducedTangentSpaceWith (c.isRetraction.baseRetraction c.relOpen) T z =
      TO c z ⊓ minimalSubspaceWith T (c.φ.toPartialEquiv x) := by
  change TO c z ⊓ minimalSubspaceWith T (c.φ.model.E.toBase 1 z) = _
  rw [hz]

/-- **The definitions agree** (at every point, not only at zeros): the project's
`IsGeneralPositionGerm` is B's `IsGeneralPositionB`. -/
theorem gp_iff (Bd : StrongBundle PX P) (f : X → Y) (x : X) :
    Bd.IsGeneralPositionGerm f x ↔ IsGeneralPositionB Bd f x := by
  constructor
  · rintro ⟨c, hc, hxc, z, hz, hsurj, hgen⟩
    refine ⟨c, hc, hxc, z, hz, fun k hk => ?_, fun {n W} T hT => ?_⟩
    · obtain ⟨u, hu⟩ := hsurj k hk
      exact ⟨u.1, u.2, hu⟩
    · obtain ⟨Bc, hBc, hsc, hsplit⟩ := hgen T hT
      refine ⟨Bc, ?_, hsc, fun m => ?_⟩
      · rw [← reduced_eq c z hz T]; exact hBc
      · rw [← linKer_eq]; exact hsplit m
  · rintro ⟨c, hc, hxc, z, hz, hsurj, hgen⟩
    refine ⟨c, hc, hxc, z, hz, fun k hk => ?_, fun {n W} T hT => ?_⟩
    · obtain ⟨u, hu, huk⟩ := hsurj k hk
      exact ⟨⟨u, hu⟩, huk⟩
    · obtain ⟨Bc, hBc, hsc, hsplit⟩ := hgen T hT
      refine ⟨Bc, ?_, hsc, fun m => ?_⟩
      · rw [reduced_eq c z hz T]; exact hBc
      · rw [linKer_eq]; exact hsplit m

end Glue

/-- `A ⇒ B`: B (the agreement of the two definitions at zeros) is proved outright by `gp_iff`;
A (a projection of the definition) is not needed. -/
theorem A_to_B : A → B := by
  intro _ X _ _ _ PX Y _ _ _ P _ _ Bd f x _
  exact gp_iff Bd f x

/-- `B ⇒ A`: A is the projection of Definition 5.17 to its surjectivity clause, re-proved
directly (B only speaks of zeros, A of all points). -/
theorem B_to_A : B → A := by
  intro _ X _ _ _ PX Y _ _ _ P _ _ Bd f y h
  obtain ⟨c, hc, hyV, z, hz, hsurj, -⟩ := h
  exact ⟨c, hc.1, hyV, z, hz, hsurj⟩

#rt_check RoundTrip.V5_31.A_to_B [Polyfold.StrongBundle.IsGeneralPositionGerm.isLinSurjAt]
#rt_check RoundTrip.V5_31.B_to_A [Polyfold.StrongBundle.IsGeneralPositionGerm.isLinSurjAt]
#rt_overlap RoundTrip.V5_31.B_to_A [Polyfold.StrongBundle.IsGeneralPositionGerm.isLinSurjAt]

end RoundTrip.V5_31
