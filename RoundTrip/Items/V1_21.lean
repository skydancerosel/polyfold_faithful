import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V1_21

/-! Round trip for V1_21 (Definition 1.23: the degeneracy index of a partial quadrant).

`A` is the conjunction of the types of the theorems in the item's declaration list,
`degIndex_eq` and `degIndex_quadrant` (`quadrantDeg`, `degIndexWith`, `degIndex` are definitions,
the vocabulary).  None has universe parameters (`ScBanach` lives in `Type`).

`B` reads the definition as "the count `#{i : a_i = 0}` does not depend on the presentation `T`",
for a `d_C` computed with a chosen presentation.  The blind file's own definitions agree with the
project's definitionally: `Presentation E C` is the data of `IsPartialQuadrant E C`
(`{p | ∀ i, 0 ≤ p.1 i}` is `quadrant n W 0` by `rfl`), `degWith T x` is `degIndexWith T x`
(`quadrantDeg (T 0 x)`) by `rfl`, and `degC` / `degIndex` both use a chosen presentation
(`0` if there is none); they differ only in which presentation is chosen, which `B` / `A` make
irrelevant on `C`. -/

namespace RoundTrip.V1_21
open Polyfold

/-- The project's statement. -/
def A : Prop :=
  (type_of% @Polyfold.degIndex_eq) ∧ (type_of% @Polyfold.degIndex_quadrant)

theorem A_holds : A := ⟨@Polyfold.degIndex_eq, @Polyfold.degIndex_quadrant⟩

/-- The blind `degWith` is the project's `degIndexWith`. -/
theorem degWith_eq {E : ScBanach} {k : ℕ} {W : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin k → ℝ)).prod W)) (x : E 0) :
    degWith T x = degIndexWith T x := rfl

/-- A presentation is the data of `IsPartialQuadrant`. -/
theorem nonempty_presentation_iff (E : ScBanach) (C : Set (E 0)) :
    Nonempty (Presentation E C) ↔ IsPartialQuadrant E C :=
  ⟨fun ⟨P⟩ => ⟨P.k, P.W, P.T, P.eq⟩, fun ⟨n, W, T, hT⟩ => ⟨⟨n, W, T, hT⟩⟩⟩

theorem A_to_B : A → B := by
  intro hA E C P x hx
  have hne : Nonempty (Presentation E C) := ⟨P⟩
  unfold degC
  rw [dif_pos hne]
  have h1 := hA.1 hne.some.T hne.some.eq hx
  have h2 := hA.1 P.T P.eq hx
  rw [degWith_eq, degWith_eq, ← h1, ← h2]

/-- From `B`: the count is the same for any two presentations (Lemma 1.24). -/
theorem B_indep (hB : B) {E : ScBanach} {C : Set (E 0)} {n n' : ℕ} {W W' : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W))
    (T' : ScIso E ((ScBanach.const (Fin n' → ℝ)).prod W')) (hT : C = T 0 ⁻¹' quadrant n W 0)
    (hT' : C = T' 0 ⁻¹' quadrant n' W' 0) {x : E 0} (hx : x ∈ C) :
    degIndexWith T x = degIndexWith T' x := by
  have h1 := hB E C ⟨n, W, T, hT⟩ x hx
  have h2 := hB E C ⟨n', W', T', hT'⟩ x hx
  rw [← degWith_eq, ← degWith_eq]
  exact h1.symm.trans h2

theorem B_degIndex_eq (hB : B) {E : ScBanach} {C : Set (E 0)} {n : ℕ} {W : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (hT : C = T 0 ⁻¹' quadrant n W 0)
    {x : E 0} (hx : x ∈ C) : degIndex E C x = degIndexWith T x := by
  have h : IsPartialQuadrant E C := ⟨n, W, T, hT⟩
  rw [degIndex, dif_pos h]
  exact B_indep hB _ T h.choose_spec.choose_spec.choose_spec hT hx

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun {E C n W} T hT {x} hx => B_degIndex_eq hB T hT hx, ?_⟩
  intro n W p hp
  exact B_degIndex_eq hB (ScIso.refl _) (by ext; rfl) hp

#rt_check RoundTrip.V1_21.A_to_B [Polyfold.degIndex_eq, Polyfold.degIndex_quadrant]
#rt_check RoundTrip.V1_21.B_to_A [Polyfold.degIndex_eq, Polyfold.degIndex_quadrant]
#rt_overlap RoundTrip.V1_21.B_to_A [Polyfold.degIndex_eq, Polyfold.degIndex_quadrant]

end RoundTrip.V1_21
