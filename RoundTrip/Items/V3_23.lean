import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_23

/-! Round trip for V3_23 (Proposition 3.26: invariance of the tangent germ property).

`A` is the conjunction of the types of `proposition_3_2_2` and `proposition_3_2_2_image` (universes
of `X`, `X'` instantiated at `0`); `TangentGermChart.transport` is a definition.

* Neither direction is derived from the other side (`A_to_B` below is VACUOUS: `fun _ => B_holds`).  `A` is about the project's notion `HasTangentGermProperty`, `B`
  about the text's (`HasTangentGermPropertyB`), and the two notions are only known to agree in one
  direction (text ⇒ project, `RoundTrip/Items/V3_22.lean`, `mpr_of_A`); the converse needs the
  germ version of Proposition 1.19 (to turn the project's `k`-dependent neighbourhoods of
  `IsScInftyGermAt` into one sc-germ of neighbourhoods) and closed ⇒ sc-complement (proved in
  `V3_20.lean`).  Going through the notions in both directions is therefore effort, not a genuine
  difference in the invariance statement.
* **`B` is true** (`B_holds`, proved outright, NOT from `A`): the text's data at `x` are carried to
  `ψ(x)` by the chart `ϕ ∘ ψ⁻¹` (the project's `transportChart`) with the same `N, Y, V, δ, G, D`,
  and `ψ(M) ⊆ X'_∞` because sc-smooth maps preserve the levels; this is word for word the
  project's proof (`TangentGermChart.transport`), applied to the text's notion.  `B`'s
  tameness hypothesis on `X` is not used (neither is it in `A`).
-/

namespace RoundTrip.V3_23
open Polyfold Set

/-- The project's statement (universes of `X`, `X'` at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.proposition_3_2_2.{0, 0}) ∧ (type_of% @Polyfold.proposition_3_2_2_image.{0, 0})

theorem A_holds : A := ⟨@Polyfold.proposition_3_2_2.{0, 0}, @Polyfold.proposition_3_2_2_image.{0, 0}⟩

/-- The text's data are carried by an sc-diffeomorphism (the project's construction
`TangentGermChart.transport`, redone for `HasTangentGermPropertyB`). -/
theorem transportB {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    {PX : MPolyfold X} {X' : Type} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X']
    {PX' : MPolyfold X'} {ψ : X → X'} {ψ' : X' → X}
    (h : PX.IsScDiffeoOn PX' ψ ψ' univ univ) {M : Set X} {n : ℕ}
    (hM : HasTangentGermPropertyB PX M n) : HasTangentGermPropertyB PX' (ψ '' M) n := by
  obtain ⟨hMs, hx⟩ := hM
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxs := hMs hx
    rw [MPolyfold.smoothSet, mem_iInter] at hxs ⊢
    intro m
    exact (h.isScSmoothOn.mapsTo_levelSet m) ⟨mem_univ _, hxs m⟩
  · rintro _ ⟨x, hxM, rfl⟩
    obtain ⟨φ, hφ, hxs, hφ0, htame, N, Yc, hfin, hrank, hsmooth, hint, hYc, V, hV, h0V,
      δ, hδY, hδc, himg, hδ0, G, hGV, hGs, D, hD, hD0⟩ := hx x hxM
    refine ⟨MPolyfold.transportChart h.symm φ, MPolyfold.transportChart_isChart h.symm hφ,
      ⟨mem_univ _, by rw [mem_preimage, h.left_inv x (mem_univ _)]; exact hxs⟩, ?_, ?_,
      N, Yc, hfin, hrank, hsmooth, hint, hYc, V, hV, h0V, δ, hδY, hδc, ?_, hδ0, G, hGV, hGs, D,
      hD, hD0⟩
    · show φ.toPartialEquiv (ψ' (ψ x)) = 0
      rw [h.left_inv x (mem_univ _)]; exact hφ0
    · rw [MPolyfold.transportChart_model_O_univ]; exact htame
    · show (φ.toPartialEquiv ∘ ψ') '' (ψ '' M ∩ (univ ∩ ψ' ⁻¹' φ.source)) =
        (fun v : N => (v : φ.model.E 0) + δ v) '' V
      rw [← himg, image_comp]
      congr 1
      ext y
      constructor
      · rintro ⟨_, ⟨⟨m, hm, rfl⟩, -, hφm⟩, rfl⟩
        rw [mem_preimage, h.left_inv m (mem_univ _)] at hφm
        rw [h.left_inv m (mem_univ _)]
        exact ⟨hm, hφm⟩
      · rintro ⟨hy, hφy⟩
        refine ⟨ψ y, ⟨⟨y, hy, rfl⟩, mem_univ _, ?_⟩, h.left_inv y (mem_univ _)⟩
        rw [mem_preimage, h.left_inv y (mem_univ _)]; exact hφy

/-- **`B` holds** (outright, not from `A`). -/
theorem B_holds : B := by
  intro X _ _ _ PX X' _ _ _ PX' ψ ψ' _ h M M' hM n
  constructor
  · intro hM'
    have h1 := transportB h.symm hM'
    have hψ'M' : ψ' '' M' = M := by
      rw [← hM, image_image]
      conv_rhs => rw [← image_id M]
      exact image_congr fun x _ => h.left_inv x (mem_univ _)
    rwa [hψ'M'] at h1
  · intro hMP
    rw [← hM]; exact transportB h hMP

/-- Vacuous: `B` is proved outright (the hypothesis is not used). -/
theorem A_to_B : A → B := fun _ => B_holds

#rt_check RoundTrip.V3_23.A_to_B [Polyfold.proposition_3_2_2, Polyfold.proposition_3_2_2_image]
#rt_overlap RoundTrip.V3_23.A_to_B [Polyfold.proposition_3_2_2, Polyfold.proposition_3_2_2_image]

end RoundTrip.V3_23
