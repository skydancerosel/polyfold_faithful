import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_47

/-!
Round trip for V5_47 (Definition 5.28: sc-smooth partitions of unity).

The listed declarations `Polyfold.MPolyfold.IsScSmoothPartitionOfUnity` and
`Polyfold.MPolyfold.AdmitsScPartitionsOfUnity` are both definitions, so `A = True`; the content of
the audit is the comparison of the project's notion with B's, which is B itself, proved outright
here (`B_holds`).

The project packages the partition of unity as Mathlib's `PartitionOfUnity ι X` (continuous maps,
locally finite **supports** `{ρᵢ ≠ 0}`, `ρᵢ ≥ 0`, `Σ ρᵢ = 1`, `Σ ρᵢ ≤ 1`) plus sc-smoothness of
every `ρᵢ`; B writes the family `β : Λ → X → ℝ` directly, with locally finite **closed supports**
`tsupport`.  These agree: sc-smooth maps are continuous (`IsScSmoothOn.continuousOn`), a family
is locally finite iff the family of closures is (`LocallyFinite.closure`), and `Σ = 1` gives
`Σ ≤ 1`.  The index types live in the universe of `X` on both sides (`Type` at universe `0`).
-/

namespace RoundTrip.V5_47
open Polyfold Set Function

/-- Only definitions are listed: `A = True`. -/
def A : Prop := True

theorem A_holds : A := trivial

/-- The project's Definition 5.28 is B's (both directions). -/
theorem B_holds : B := by
  intro X _ _ _ PX
  constructor
  · intro h Λ U hUo hUcov
    obtain ⟨ρ, hρsub, hρsc⟩ := h Λ U hUo hUcov
    exact ⟨fun l => ρ l, ⟨hρsc, fun l x => ρ.nonneg l x, ρ.locallyFinite_tsupport,
      fun x => ρ.sum_eq_one (mem_univ x)⟩, hρsub⟩
  · intro h ι U hUo hUcov
    obtain ⟨β, ⟨hsc, hnn, hlf, hsum⟩, hsub⟩ := h ι U hUo hUcov
    let ρ : PartitionOfUnity ι X :=
      { toFun := fun l => ⟨β l, continuousOn_univ.1 (hsc l).continuousOn⟩
        locallyFinite' := hlf.subset fun l => subset_closure
        nonneg' := fun l x => hnn l x
        sum_eq_one' := fun x _ => hsum x
        sum_le_one' := fun x => (hsum x).le }
    exact ⟨ρ, hsub, hsc⟩

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := fun _ => trivial

#rt_check RoundTrip.V5_47.A_to_B []
#rt_check RoundTrip.V5_47.B_to_A []
#rt_overlap RoundTrip.V5_47.B_to_A []
#rt_overlap RoundTrip.V5_47.A_to_B []

end RoundTrip.V5_47
