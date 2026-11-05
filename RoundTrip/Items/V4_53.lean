import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_53

/-!
Round trip for V4_53 (§4.3: the family `ℝᵐ × X`, stratified regular points).  The item lists the
theorem `Polyfold.prod_rn_isTame` and the definitions `fibreSet`, `rnPres`, `IsStratRegularPoint`,
`IsStratRegularValue`; so `A` is the type of `prod_rn_isTame` (universe `0`).

B = (i) `ℝᵐ × X` is tame for tame `X` ∧ (ii) the project's `IsStratRegularPoint` is B's chart
reading `IsStratRegularPointB`.
* (i) is literally `A` (binder order aside): `A_to_B` uses the hypothesis for (i), `B_to_A` is
  B's first conjunct.
* (ii) is a definitional agreement, proved outright (`strat_iff`): the only difference is
  the bookkeeping of the data of Definition 4.13 (B: `V ⊆ dom ψ` and `ψ(A ∩ V)`; project: any data
  with `z ∈ V`, `z₂ ∈ dom φ` and the shrunk set `W = V ∩ dom ψ ∩ s⁻¹(V ∩ dom ψ)`).
-/

namespace RoundTrip.V4_53
open Polyfold

def A : Prop := type_of% @Polyfold.prod_rn_isTame.{0}

theorem A_holds : A := @Polyfold.prod_rn_isTame.{0}

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
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

/-- (ii): the project's stratified regular points are B's (proved outright; no tameness and no
smoothness of `A` needed). -/
theorem strat_iff (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) (m : ℕ) [ParacompactSpace ((Fin m → ℝ) × X)] (S : Set ((Fin m → ℝ) × X))
    (z : (Fin m → ℝ) × X) : IsStratRegularPoint PX S z ↔ IsStratRegularPointB PX S z := by
  constructor
  · rintro ⟨hzS, d, a, φ, n, Wq, T, y, hzV, hφ, hzφ, hT, hy, hμ⟩
    have hzψ : z ∈ ((rnChart m a).prod φ).source := ⟨Set.mem_univ _, hzφ⟩
    refine ⟨hzS, d.toSubData.shrink ((rnChart m a).prod φ), d.s, a, φ, n, Wq, T, y,
      isScPlusRetractionOn_shrink d _, ?_, d.toSubData.mem_shrink _ hzS hzV hzψ, hφ,
      d.toSubData.shrink_subset_source _, hT, hy, fun μ => ?_⟩
    · rw [Set.inter_comm]; exact d.toSubData.image_shrink _
    · obtain ⟨v, hv, h1, h2⟩ := hμ μ
      refine ⟨v, ?_, h1, h2⟩
      rw [Set.inter_comm]; exact hv
  · rintro ⟨hzS, V, s, a, φ, n, Wq, T, y, hs, himg, hzV, hφ, hVψ, hT, hy, hμ⟩
    let d : ((rnPolyfold m).prod PX).SubmanifoldData S := ⟨V, s, hs.isScSmoothOn.isOpen, hs, himg⟩
    have hshrink : d.toSubData.shrink ((rnChart m a).prod φ) = V := by
      ext x
      simp only [MPolyfold.SubData.shrink, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · exact fun h => h.1.1
      · intro hx
        exact ⟨⟨hx, hVψ hx⟩, hs.mapsTo hx, hVψ (hs.mapsTo hx)⟩
    refine ⟨hzS, d, a, φ, n, Wq, T, y, hzV, hφ, (hVψ hzV).2, hT, hy, fun μ => ?_⟩
    obtain ⟨v, hv, h1, h2⟩ := hμ μ
    refine ⟨v, ?_, h1, h2⟩
    show v ∈ tangentSpace _ _ (((rnChart m a).prod φ) '' (d.toSubData.shrink _ ∩ S)) y
    rw [hshrink, Set.inter_comm]; exact hv

theorem A_to_B : A → B := by
  intro hA
  refine ⟨fun X _ _ _ PX m _ hX => hA hX, fun X _ _ _ PX m _ S z _ _ => strat_iff X PX m S z⟩

theorem B_to_A : B → A := by
  rintro ⟨h1, -⟩ n X _ _ _ PX _ hX
  exact h1 X PX n hX

#rt_check RoundTrip.V4_53.A_to_B [Polyfold.prod_rn_isTame]
#rt_check RoundTrip.V4_53.B_to_A [Polyfold.prod_rn_isTame]
#rt_overlap RoundTrip.V4_53.B_to_A [Polyfold.prod_rn_isTame]
#rt_check RoundTrip.V4_53.strat_iff [Polyfold.prod_rn_isTame]

end RoundTrip.V4_53
