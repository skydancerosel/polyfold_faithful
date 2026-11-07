import Polyfold
/-! Blind formalization of V6_21 (the text's §6.4, Lemma 6.18, p. 215). Choices:
- Setting: real Banach spaces `E F : Type` (universe 0); the data of Lemma 6.17 (V6_20): `T`
  Fredholm, `P ∈ Π_T` (the project's `IsGoodLeftProj`, checked with `#print`: `P² = P`,
  `dim F/R(P) < ∞`, `R(PT) = R(P)`), `Y` a topological complement of `K = ker(PT)` (Mathlib's
  `Submodule.IsTopCompl`), and `ε > 0` for which the conclusions of Lemma 6.17 hold: for
  `‖S − T‖ < ε`, `P ∈ Π_S` and `y ↦ PSy` is a topological isomorphism `Y ≅ R(P)`.  (Any such `ε`,
  not only the one produced by the proof of Lemma 6.17.)
- `y(k, S) = −(PS|_Y)⁻¹ PSk`: rendered as a map `y : ball × K → E` characterized by
  `y(k,S) ∈ Y` and `PS(k + y(k,S)) = 0` (by (2) of Lemma 6.17 this is exactly
  `−(PS|_Y)⁻¹PSk`); claimed to exist, to be linear in `k`, and continuous in `(k, S)` jointly on
  `{‖S − T‖ < ε} × K` (`k` ranges over `ker(PT)`, as in the bijection).
- "the space `⋃ {S} × ker(PS)` with its projection has the structure of a trivial vector bundle":
  `(S, k) ↦ (S, k + y(k,S))` is a homeomorphism from `ball × K` onto the subspace
  `{(S, x) | PSx = 0}` of `ball × E` (fibrewise linear by the linearity of `y`), whose inverse is
  `(S, k + y) ↦ (S, k)`, i.e. `(S, x) ↦ (S, π_K x)` with `π_K` the projection onto `K` along `Y`.
  The text says "continuous bijection with inverse …"; I also claim the inverse is continuous
  (part of "trivial vector bundle").
- Nothing looks false to me.
-/
namespace RoundTrip.V6_21
open Polyfold

/-- Lemma 6.18: `y(k,S) = −(PS|_Y)⁻¹PSk` is continuous, and `(S, k) ↦ (S, k + y(k,S))`
trivializes `⋃_{‖S−T‖<ε} {S} × ker(PS)` over the ball, with inverse `(S, k + y) ↦ (S, k)`. -/
def B : Prop :=
  ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) (P : F →L[ℝ] F) (Y : Submodule ℝ E) (ε : ℝ),
    T.IsFredholm → IsGoodLeftProj T P →
    ∀ hY : Submodule.IsTopCompl (LinearMap.ker ((P.comp T : E →L[ℝ] F) : E →ₗ[ℝ] F)) Y,
    0 < ε →
    (∀ S : E →L[ℝ] F, ‖S - T‖ < ε →
      IsGoodLeftProj S P ∧
      ∃ e : Y ≃L[ℝ] LinearMap.range (P : F →ₗ[ℝ] F), ∀ y : Y, (e y : F) = P (S y)) →
    ∃ y : Metric.ball T ε → LinearMap.ker ((P.comp T : E →L[ℝ] F) : E →ₗ[ℝ] F) → E,
      (∀ S k, y S k ∈ Y ∧ P ((S : E →L[ℝ] F) ((k : E) + y S k)) = 0) ∧
      (∀ S, IsLinearMap ℝ (y S)) ∧
      Continuous (fun p : Metric.ball T ε × LinearMap.ker ((P.comp T : E →L[ℝ] F) : E →ₗ[ℝ] F) =>
        y p.1 p.2) ∧
      ∃ Φ : (Metric.ball T ε × LinearMap.ker ((P.comp T : E →L[ℝ] F) : E →ₗ[ℝ] F)) ≃ₜ
          {p : Metric.ball T ε × E //
            p.2 ∈ LinearMap.ker ((P.comp (p.1 : E →L[ℝ] F) : E →L[ℝ] F) : E →ₗ[ℝ] F)},
        (∀ S k, (Φ (S, k) : Metric.ball T ε × E) = (S, (k : E) + y S k)) ∧
        (∀ q, Φ.symm q = (q.1.1,
          (LinearMap.ker ((P.comp T : E →L[ℝ] F) : E →ₗ[ℝ] F)).projectionOnto Y hY.isCompl q.1.2))

end RoundTrip.V6_21
