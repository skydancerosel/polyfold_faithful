import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_56

/-!
Round trip for V7_56 (Definition 7.16: ep-groupoids with sc-smooth partitions of unity).

Only definitions are listed (`EpGroupoid.HasScPartitionsOfUnity`,
`MPolyfold.IsScSmoothPartitionOfUnity`), so `A = True`; the content of the audit is B itself, the
agreement of the project's `HasScPartitionsOfUnity` with B's hand-written `HasScPUB`, proved
outright here (`B_holds`).  The two agree field by field: the same Mathlib `PartitionOfUnity`
indexed by a type in the universe of `Obj` (`Type` at universe `0`), `IsSubordinate`, sc-smooth
`β_λ : X → ℝ` (`IsScSmoothPartitionOfUnity` is `∀ i, IsScSmoothMap realPolyfold (β i)`),
saturated (`GroupoidStr.IsSaturated` is literally `π⁻¹(π(W)) = W`) open neighbourhoods meeting
finitely many `tsupport`s; the only rephrasing is invariance, `β(s φ) = β(t φ)` for all morphisms
`φ` versus B's `β z = β y` whenever some `φ : y → z`.
-/

namespace RoundTrip.V7_56
open Polyfold

/-- Only definitions are listed: `A = True`. -/
def A : Prop := True

theorem A_holds : A := trivial

/-- The project's Definition 7.16 is B's (both directions). -/
theorem B_holds : B := by
  intro Obj Mor _ _ _ _ _ _ X
  constructor
  · intro h Λ U hUo hUs hcov
    obtain ⟨β, hsub, hsm, hW, hinv⟩ := h Λ U hUo hUs hcov
    exact ⟨β, hsub, hsm, hW, fun l y z ⟨φ, hy, hz⟩ => hy ▸ hz ▸ (hinv l φ).symm⟩
  · intro h ι U hUo hUs hcov
    obtain ⟨β, hsub, hsm, hW, hinv⟩ := h ι U hUo hUs hcov
    exact ⟨β, hsub, hsm, hW, fun i φ => (hinv i _ _ ⟨φ, rfl, rfl⟩).symm⟩

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := fun _ => trivial

#rt_check RoundTrip.V7_56.A_to_B []
#rt_check RoundTrip.V7_56.B_to_A []
#rt_overlap RoundTrip.V7_56.B_to_A []
#rt_overlap RoundTrip.V7_56.A_to_B []

end RoundTrip.V7_56
