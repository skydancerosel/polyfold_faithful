import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V4_3

/-!
Round trip for V4_3 (a finite-dimensional sc-Banach space has only the constant sc-structure).
`A` is the conjunction of the types of `ScBanach.finiteDimensional_lvl`,
`ScBanach.toBase_surjective` and `ScBanach.mem_smooth_of_finiteDimensional` (no universe
parameters; `ScBanach.scIsoConst` is a definition, i.e. vocabulary, and is not used below since
its body contains the banned lemmas).
-/

namespace RoundTrip.V4_3
open Polyfold

def A : Prop :=
  type_of% @Polyfold.ScBanach.finiteDimensional_lvl ∧
  type_of% @Polyfold.ScBanach.toBase_surjective ∧
  type_of% @Polyfold.ScBanach.mem_smooth_of_finiteDimensional

theorem A_holds : A :=
  ⟨@Polyfold.ScBanach.finiteDimensional_lvl, @Polyfold.ScBanach.toBase_surjective,
    @Polyfold.ScBanach.mem_smooth_of_finiteDimensional⟩

/-- Existence half of B: the constant scale is an sc-structure (independent of A). -/
theorem B_existence (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ (E : ScBanach) (e : ∀ m : ℕ, E.lvl m ≃ₗᵢ[ℝ] V),
      ∀ (m : ℕ) (x : E.lvl (m + 1)), e m (E.incl m x) = e (m + 1) x :=
  ⟨ScBanach.const V, fun _ => LinearIsometryEquiv.refl ℝ V, fun _ _ => rfl⟩

theorem A_to_B : A → B := by
  rintro ⟨hfd, hsurj, -⟩
  refine ⟨fun E hE m => ?_, fun V _ _ _ => B_existence V⟩
  have := hfd E m
  let e : E.lvl m ≃L[ℝ] E.lvl 0 :=
    (LinearEquiv.ofBijective (E.toBase m : E m →ₗ[ℝ] E 0)
      ⟨E.toBase_injective m, hsurj E m⟩).toContinuousLinearEquiv
  exact ⟨e, fun x => rfl⟩

theorem B_to_A : B → A := by
  rintro ⟨huniq, -⟩
  have hfd : type_of% @Polyfold.ScBanach.finiteDimensional_lvl := by
    intro E hE m
    obtain ⟨e, -⟩ := huniq E hE m
    exact LinearEquiv.finiteDimensional e.symm.toLinearEquiv
  have hsurj : type_of% @Polyfold.ScBanach.toBase_surjective := by
    intro E hE m x
    obtain ⟨e, he⟩ := huniq E hE m
    exact ⟨e.symm x, by rw [← he, ContinuousLinearEquiv.apply_symm_apply]⟩
  refine ⟨hfd, hsurj, fun E hE x => ?_⟩
  exact (E.mem_smooth_iff).2 fun m => hsurj E m x

#rt_check RoundTrip.V4_3.A_to_B [Polyfold.ScBanach.finiteDimensional_lvl, Polyfold.ScBanach.toBase_surjective, Polyfold.ScBanach.mem_smooth_of_finiteDimensional]
#rt_check RoundTrip.V4_3.B_to_A [Polyfold.ScBanach.finiteDimensional_lvl, Polyfold.ScBanach.toBase_surjective, Polyfold.ScBanach.mem_smooth_of_finiteDimensional]
#rt_overlap RoundTrip.V4_3.B_to_A [Polyfold.ScBanach.finiteDimensional_lvl, Polyfold.ScBanach.toBase_surjective, Polyfold.ScBanach.mem_smooth_of_finiteDimensional]

end RoundTrip.V4_3
