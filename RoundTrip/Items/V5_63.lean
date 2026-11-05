import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_63

/-!
Round trip for V5_63 (Corollary 5.44).  `A` is the conjunction of the types of
`Polyfold.corollary_5_44` (no universe parameter) and
`Polyfold.MPolyfold.admitsScPartitionsOfUnity_of_hilbert` (universe instantiated at `0`).

* "Hilbert": the project asks `∃ b, ∀ v, ‖v‖² = b v v` (a continuous bilinear `b`, not assumed
  symmetric); B asks for a *symmetric* `b` with `b x x = ‖x‖²`.  These agree: symmetrize
  `b' = (b + bᵀ)/2` (`hilbert_iff`).
* The genuine difference: `corollary_5_44` has the cited Theorem 5.43
  (`GodefroyTroyanskiWhitfieldZizlerStatement (M.E 0) ⊤`) as an **explicit hypothesis**, B has
  none.  So `B → A` is immediate (B's conclusion, extra hypothesis dropped; the M-polyfold
  conjunct then follows from Theorem 5.37 "(ii) ⇒ (i)", `admitsScPartitionsOfUnity_of_approx`), but
  `A → B` would need Theorem 5.43 for Hilbert spaces (that Hilbert spaces admit `C^∞` partitions of
  unity), deep Banach-space geometry not in the project or Mathlib.  Not proved.
* With the cited theorem assumed (the blind file's `BCited`), `A → BCited` is proved.
-/

namespace RoundTrip.V5_63
open Polyfold

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.corollary_5_44) ∧
  (type_of% @Polyfold.MPolyfold.admitsScPartitionsOfUnity_of_hilbert.{0})

theorem A_holds : A :=
  ⟨@Polyfold.corollary_5_44, @Polyfold.MPolyfold.admitsScPartitionsOfUnity_of_hilbert.{0}⟩

/-- The two readings of "the norm comes from an inner product" agree. -/
theorem hilbert_iff (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (∃ b : V →L[ℝ] V →L[ℝ] ℝ, ∀ v, ‖v‖ ^ 2 = b v v) ↔ IsHilbertNormB V := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨(1 / 2 : ℝ) • (b + b.flip), fun x y => ?_, fun x => ?_⟩
    · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.flip_apply]
      ring
    · simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.flip_apply, ← hb, smul_eq_mul]
      ring
  · rintro ⟨b, -, hb⟩
    exact ⟨b, fun v => (hb v).symm⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun M hH _ => hB M ((hilbert_iff _).1 hH), fun {X} _ _ _ {PX} h => ?_⟩
  refine admitsScPartitionsOfUnity_of_approx
    (S := {φ | PX.IsChart φ ∧ ∃ b : φ.model.E 0 →L[ℝ] φ.model.E 0 →L[ℝ] ℝ, ∀ v, ‖v‖ ^ 2 = b v v})
    (fun φ hφ => hφ.1) (fun x => ?_) (fun φ hφ => hB φ.model ((hilbert_iff _).1 hφ.2))
  obtain ⟨φ, hφ, hx, hb, -⟩ := h x
  exact ⟨φ, ⟨hφ, hb⟩, hx⟩

/-- With the cited Theorem 5.43 assumed for every Banach space (the blind file's `BCited`). -/
theorem A_to_BCited : A → BCited := by
  intro hA h543 M hM
  exact hA.1 M ((hilbert_iff _).2 hM) (h543 _ ⊤)

#rt_check RoundTrip.V5_63.B_to_A [Polyfold.corollary_5_44,
  Polyfold.MPolyfold.admitsScPartitionsOfUnity_of_hilbert]
#rt_check RoundTrip.V5_63.A_to_BCited [Polyfold.corollary_5_44,
  Polyfold.MPolyfold.admitsScPartitionsOfUnity_of_hilbert]
#rt_overlap RoundTrip.V5_63.B_to_A [Polyfold.corollary_5_44,
  Polyfold.MPolyfold.admitsScPartitionsOfUnity_of_hilbert]

end RoundTrip.V5_63
