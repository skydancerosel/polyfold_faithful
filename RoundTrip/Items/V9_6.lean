import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V9_6

/-! Round trip for V9_6 (Definition 9.1.6, p. 404 [2017: Definition 9.2, p. 293]: closed and
compact `Θ`).

`A` is the type of the one listed theorem, `EpGroupoid.isCompactBranched_indicator` (the
indicator of a point of `ℝⁿ` is compact; no universe parameters).  The listed
`EpGroupoid.IsClosedBranched`, `EpGroupoid.IsCompactBranched` are definitions (vocabulary).

* `B` says the two project definitions are `IsClosed (π '' suppB Θ)` and
  `IsCompact (π '' suppB Θ)`.  Both hold by `Iff.rfl` (`orbitSupp Θ = π '' supp Θ`,
  `supp = suppB`), so `A → B` is proved without the hypothesis.
* `B → A`: through `B` the claim becomes compactness of `π '' suppB 1_{p}`; `suppB 1_{p} = {p}`
  and the image of a point is compact.  The definitional comparison is the content; `A` itself
  is a witness of satisfiability, not a consequence of `B`. -/

namespace RoundTrip.V9_6
open Polyfold

/-- The project's statement. -/
def A : Prop := type_of% @Polyfold.EpGroupoid.isCompactBranched_indicator

theorem A_holds : A := @Polyfold.EpGroupoid.isCompactBranched_indicator

/-- `B` is definitional. -/
theorem B_holds : B := fun _ _ _ _ _ _ _ _ _ _ => ⟨Iff.rfl, Iff.rfl⟩

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := by
  intro hB n p
  refine ((hB _ _ (EpGroupoid.trivial (rnPolyfold n)) _).2).2 ?_
  have hs : suppB (({p} : Set (Fin n → ℝ)).indicator (1 : (Fin n → ℝ) → ℚ)) = {p} := by
    ext y
    by_cases hy : y = p
    · subst hy; simp [suppB]
    · simp [suppB, hy]
  rw [hs, Set.image_singleton]
  exact isCompact_singleton

#rt_check RoundTrip.V9_6.A_to_B [Polyfold.EpGroupoid.isCompactBranched_indicator]
#rt_check RoundTrip.V9_6.B_to_A [Polyfold.EpGroupoid.isCompactBranched_indicator]
#rt_overlap RoundTrip.V9_6.B_to_A [Polyfold.EpGroupoid.isCompactBranched_indicator]

end RoundTrip.V9_6
