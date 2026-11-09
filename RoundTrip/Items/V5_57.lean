import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_57

/-!
Round trip for V5_57 (Theorem 5.37).  `A` is the type of `Polyfold.theorem_5_5_10`, universe
instantiated at `0`.

Both sides use the same notions (`MPolyfold.AdmitsScPartitionsOfUnity`,
`LocalModel.HasApproxProperty`).  The only difference is how "an atlas" is written:

* A: a set `S` of charts of the M-polyfold structure (`PX.IsChart`, compatible with the given
  atlas) covering `X`;
* B: an `MAtlas` equivalent to `PX.atlas` (`MAtlas.Equiv`).

These are the same thing (`exists_atlas_iff`): charts of the structure are pairwise compatible
(`MPolyfold.IsChart.compatible`), so a covering set of them is an atlas equivalent to `PX.atlas`
(`MAtlas.equiv_iff`); conversely every chart of an equivalent atlas is compatible with `PX.atlas`.
-/

namespace RoundTrip.V5_57
open Polyfold

/-- The project's statement, universe `0`. -/
def A : Prop := type_of% @Polyfold.theorem_5_5_10.{0}

theorem A_holds : A := @Polyfold.theorem_5_5_10.{0}

/-- A covering set of charts of the structure is the same as an atlas equivalent to `PX.atlas`. -/
theorem exists_atlas_iff {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    (PX : MPolyfold X) (Q : MChart X → Prop) :
    (∃ S : Set (MChart X), (∀ φ ∈ S, PX.IsChart φ) ∧ (∀ x, ∃ φ ∈ S, x ∈ φ.source) ∧
      ∀ φ ∈ S, Q φ) ↔
    ∃ A : MAtlas X, A.Equiv PX.atlas ∧ ∀ φ ∈ A.charts, Q φ := by
  constructor
  · rintro ⟨S, hS, hcov, hQ⟩
    refine ⟨⟨S, fun φ hφ ψ hψ => MPolyfold.IsChart.compatible PX (hS φ hφ) (hS ψ hψ), hcov⟩,
      (MAtlas.equiv_iff _ _).2 fun φ hφ ψ hψ => hS φ hφ ψ hψ, hQ⟩
  · rintro ⟨A, hA, hQ⟩
    exact ⟨A.charts, fun φ hφ ψ hψ => (MAtlas.equiv_iff _ _).1 hA φ hφ ψ hψ, A.cover, hQ⟩

theorem A_to_B : A → B := by
  intro hA X _ _ _ PX
  rw [← exists_atlas_iff]
  exact @hA X _ _ _ PX

theorem B_to_A : B → A := by
  intro hB X _ _ _ PX
  rw [exists_atlas_iff]
  exact hB X PX

#rt_check RoundTrip.V5_57.A_to_B [Polyfold.theorem_5_5_10]
#rt_check RoundTrip.V5_57.B_to_A [Polyfold.theorem_5_5_10]
#rt_overlap RoundTrip.V5_57.B_to_A [Polyfold.theorem_5_5_10]

end RoundTrip.V5_57
