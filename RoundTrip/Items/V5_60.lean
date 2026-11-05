import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_60

/-!
Round trip for V5_60 (Definition 5.41).  The item lists only the definitions `Polyfold.IsWCG` and
`Polyfold.IsReflexive`, so `A = True`; the comparison is B itself, proved outright (`B_holds`):
the project's `IsWCG V` is B's `IsWCGB V`.

The only difference is how "weakly compact" is written: the project asks
`toWeakSpace ℝ V '' K` to be compact in Mathlib's `WeakSpace ℝ V`, B asks `K` to be compact for
its own `weakTopB V = ⨅ ℓ, induced ℓ`.  The identity `toWeakSpace` is a homeomorphism
`(V, weakTopB) ≃ WeakSpace ℝ V` (both are the coarsest topology making every `ℓ ∈ V*`
continuous), so the two conditions agree.  (`IsReflexive` is not used by B.)
-/

namespace RoundTrip.V5_60
open Polyfold Set

def A : Prop := True

theorem A_holds : A := trivial

section
variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `toWeakSpace : (V, weakTopB) → WeakSpace ℝ V` is continuous. -/
theorem continuous_to :
    @Continuous V (WeakSpace ℝ V) (weakTopB V) _ (toWeakSpace ℝ V) := by
  refine @WeakBilin.continuous_of_continuous_eval _ _ _ _ _ _ _ _ _ _ _ (weakTopB V) _
    fun ℓ => ?_
  exact continuous_iInf_dom (i := ℓ) continuous_induced_dom

/-- `toWeakSpace⁻¹ : WeakSpace ℝ V → (V, weakTopB)` is continuous. -/
theorem continuous_from :
    @Continuous (WeakSpace ℝ V) V _ (weakTopB V) (toWeakSpace ℝ V).symm := by
  refine continuous_iInf_rng.2 fun ℓ => continuous_induced_rng.2 ?_
  exact WeakBilin.eval_continuous _ ℓ

theorem isCompact_iff (K : Set V) :
    IsCompact (toWeakSpace ℝ V '' K) ↔ @IsCompact V (weakTopB V) K := by
  constructor
  · intro h
    have h' := @IsCompact.image (WeakSpace ℝ V) V _ (weakTopB V) _ _ h (continuous_from V)
    rwa [image_image, show (fun x => (toWeakSpace ℝ V).symm (toWeakSpace ℝ V x)) = id from
      funext fun x => (toWeakSpace ℝ V).symm_apply_apply x, image_id] at h'
  · intro h
    exact @IsCompact.image V (WeakSpace ℝ V) (weakTopB V) _ _ _ h (continuous_to V)

end

/-- B holds outright: the project's WCG spaces are B's. -/
theorem B_holds : B := by
  intro V _ _ _
  unfold IsWCG IsWCGB
  simp only [isCompact_iff]

/-- Vacuous: `B` is proved outright. -/
theorem A_to_B : A → B := fun _ => B_holds

/-- Vacuous: `A = True`. -/
theorem B_to_A : B → A := fun _ => trivial

#rt_check RoundTrip.V5_60.A_to_B []
#rt_check RoundTrip.V5_60.B_to_A []
#rt_overlap RoundTrip.V5_60.B_to_A []
#rt_check RoundTrip.V5_60.B_holds []

end RoundTrip.V5_60
