import Polyfold
/-! Blind formalization of V6_20 (the text's §6.4, Lemma 6.17, p. 214). Choices:
- Setting: real Banach spaces `E F : Type` (universe 0); `T : E → F` bounded Fredholm (Mathlib's
  `ContinuousLinearMap.IsFredholm`); the operator norm on `L(E, F)`.
- `Π_T` (Definition 6.9): the project's `IsGoodLeftProj T P` (checked with `#print`: `P ∘ P = P`,
  `F ⧸ R(P)` finite-dimensional, `R(P ∘ T) = R(P)`), a bounded `P : F →L[ℝ] F`.
- "a topological complement `Y` of `ker(PT)` in `E`": Mathlib's `Submodule.IsTopCompl` (algebraic
  complements with continuous projection onto `ker(PT)` along `Y`).
- (2) "`PS|_Y : Y → R(P)` is a topological isomorphism": there is a continuous linear equivalence
  `e : Y ≃L R(P)` whose underlying map is `y ↦ P S y`.
- `ε` depends on `T`, `P`, `Y`; the conclusions hold for every `S` with `‖S − T‖ < ε` (no
  Fredholm hypothesis on `S`).
- Nothing looks false to me.
-/
namespace RoundTrip.V6_20
open Polyfold

/-- Lemma 6.17: for Fredholm `T`, `P ∈ Π_T` and a topological complement `Y` of `ker(PT)` there is
`ε > 0` with `P ∈ Π_S` and `PS|_Y : Y ≅ R(P)` for all `‖S − T‖ < ε`. -/
def B : Prop :=
  ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) (P : F →L[ℝ] F) (Y : Submodule ℝ E),
    T.IsFredholm → IsGoodLeftProj T P →
    Submodule.IsTopCompl (LinearMap.ker ((P.comp T : E →L[ℝ] F) : E →ₗ[ℝ] F)) Y →
    ∃ ε > 0, ∀ S : E →L[ℝ] F, ‖S - T‖ < ε →
      IsGoodLeftProj S P ∧
      ∃ e : Y ≃L[ℝ] LinearMap.range (P : F →ₗ[ℝ] F), ∀ y : Y, (e y : F) = P (S y)

end RoundTrip.V6_20
