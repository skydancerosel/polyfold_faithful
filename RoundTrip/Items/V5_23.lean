import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_23

namespace RoundTrip.V5_23
open Polyfold

/-- The project's statement: the only theorem among the decls is the chart independence of the
surjectivity of the linearization, `IsLinSurjAt.linAt_surjective` (universes instantiated at
`0`); `IsTransversal` is vocabulary. -/
def A : Prop := type_of% @Polyfold.StrongBundle.IsLinSurjAt.linAt_surjective.{0, 0}

theorem A_holds : A := @Polyfold.StrongBundle.IsLinSurjAt.linAt_surjective.{0, 0}

/-- `A ⇒ B`.  (⇒) a zero where `IsLinSurjAt` holds lies in `X₁` (the level-`1` point of the
chart of `IsLinSurjAt`), so every chart around it has a level-`1` lift `z`, and A carries the
surjectivity to that chart; `linAt` on `rangeS (scDeriv U (r R) z)` is B's `Dg` on `TO c z`.
(⇐) take a chart of the atlas around the zero; B's surjectivity there is `IsLinSurjAt`. -/
theorem A_to_B : A → B := by
  intro hA X _ _ _ PX Y _ _ _ P _ _ Bd g hg
  constructor
  · intro htr x hx0 c hc hxc
    obtain ⟨c0, -, hxc0, z0, hz0, -⟩ := htr x hx0
    have hlev : x ∈ PX.levelSet 1 := ⟨c0.φ, c0.isChart, hxc0, z0, hz0⟩
    obtain ⟨z, hz⟩ := (PX.mem_levelSet_iff c.isChart hxc).1 hlev
    refine ⟨z, hz, fun k hk => ?_⟩
    obtain ⟨v, hv⟩ := hA hg hx0 (htr x hx0) hc hxc hz k hk
    exact ⟨v.1, v.2, hv⟩
  · intro hB x hx0
    obtain ⟨c, hc, hxc⟩ := StrongBundle.exists_chart_mem Bd x
    obtain ⟨z, hz, hsurj⟩ := hB x hx0 c (Bd.isChart_of_mem hc) hxc
    refine ⟨c, Bd.isChart_of_mem hc, hxc, z, hz, fun k hk => ?_⟩
    obtain ⟨v, hv, hvk⟩ := hsurj k hk
    exact ⟨⟨v, hv⟩, hvk⟩

/-! `B ⇒ A` is not proved: B is a statement about sections transversal at ALL their zeros
(`IsTransversal g ↔ IsTransversalB g`), A is the pointwise chart independence at ONE zero `y`
where `IsLinSurjAt f y` holds, with nothing assumed at the other zeros.  Getting A from B would
need a localization (a section agreeing with `f` near `y` with no non-transversal zeros, or a
restriction of the bundle to a neighbourhood of `y` containing no other bad zeros), which is not
available; zeros may accumulate at `y`.  The (⇐) half of B is proved without A. -/

#rt_check RoundTrip.V5_23.A_to_B [Polyfold.StrongBundle.IsLinSurjAt.linAt_surjective]

end RoundTrip.V5_23
