import Polyfold
/-! Blind formalization of V6_24 (the text's §6.4, p. 217). Choices:
- B is the conjunction of (1) every Fredholm `T` has an admissible `(T, P, ε)` ("Proposition
  6.20 gives `ε > 0` and `P ∈ Π_T`", i.e. `Π_T ≠ ∅`, a complement `Y`, and `ε` from Lemma 6.17),
  and (2) for EVERY admissible `(T, P, ε)`, `γ_(T,P,ε)` is a bijection from `DET(E, F)` over the
  ball onto `DET(T, P, ε)` (fibrewise linear by construction).  (2) is stated for every admissible
  triple, not only the one of (1), since the text uses `γ_(T,P,ε)` for all of them afterwards
  (Definition 6.22); it contains in particular that every `S` of the ball is Fredholm.
- No topology is involved in this item.
- Setting: real Banach spaces `E F : Type` (universe 0); `L(E, F)` with the operator norm; the
  ball `{‖S − T‖ < ε}` is `Metric.ball T ε` with the subspace topology.  Fredholm is Mathlib's
  `ContinuousLinearMap.IsFredholm` (for Banach spaces the text's notion).
- `DET(T, P, ε)` is "defined" for the admissible triples `IsDetChart T P ε`: `T` Fredholm,
  `P ∈ Π_T`, `ε > 0`, and for some topological complement `Y` of `ker(PT)` (Mathlib's
  `Submodule.IsTopCompl`) the conclusions of Lemma 6.17 hold on the ball (`P ∈ Π_S`, and
  `y ↦ PSy` is a topological isomorphism `Y ≅ R(P)`).  Every such `ε` is allowed, not only the
  one produced by the proof of Lemma 6.17.  (These conditions imply that every `S` of the ball is
  Fredholm; I do not add this as a hypothesis.)
- Project definitions used (checked with `#print`): `fredholmDet`, `IsGoodLeftProj` (`Π_T`:
  `P² = P`, `dim F/R(P) < ∞`, `R(PT) = R(P)`), `FredholmOp`.
- `DET(E, F) = ⋃_S {S} × det(S)`: `Bundle.TotalSpace ℝ DETF` over the project's
  `FredholmOp E F` (checked with `#print`: the subtype `{S // S.IsFredholm}` of `L(E, F)`, with
  the subspace topology of the norm topology); the fibre `DETF S` is `fredholmDet S` with the
  tensor product's linear structure.  I do not use the project's topology on `DET(E, F)`; every
  topology is passed explicitly.
- `γ_(T,P,ε)` (`gammaChart`) is defined on the points of `DET(E, F)` over the ball (`S` Fredholm,
  `‖S − T‖ < ε`), with values in `DET(T, P, ε)` (over the whole ball); fibrewise it is the linear
  isomorphism `γ^P_S`, so it is fibrewise linear by construction.
- `γ^P_T : det(T) → det(PT)` is the project's `gammaProj` (only its type was checked; its
  docstring: `Φ_{E(T,P)}` of the exact sequence `E(T,P)` followed by `λ*(F/R(P)) = λ*(F/R(PT))`).
  I did not re-derive this map; I take it to be the text's `γ^P_T`.
- Nothing looks false to me.
-/
namespace RoundTrip.V6_24
open Polyfold Bundle

noncomputable section

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- `ker(PS)`. -/
abbrev kerPS (P : F →L[ℝ] F) (S : E →L[ℝ] F) : Submodule ℝ E :=
  LinearMap.ker ((P.comp S : E →L[ℝ] F) : E →ₗ[ℝ] F)

/-- `(T, P, ε)` is admissible, i.e. `DET(T, P, ε)` is defined: `T` Fredholm, `P ∈ Π_T`, `ε > 0`,
and the conclusions of Lemma 6.17 hold on the ball `‖S − T‖ < ε` for some topological complement
`Y` of `ker(PT)`: `P ∈ Π_S`, and `y ↦ PSy` is a topological isomorphism `Y ≅ R(P)`. -/
def IsDetChart (T : E →L[ℝ] F) (P : F →L[ℝ] F) (ε : ℝ) : Prop :=
  T.IsFredholm ∧ IsGoodLeftProj T P ∧ 0 < ε ∧
  (∀ S : E →L[ℝ] F, ‖S - T‖ < ε → IsGoodLeftProj S P) ∧
  ∃ Y : Submodule ℝ E, Submodule.IsTopCompl (kerPS P T) Y ∧
    ∀ S : E →L[ℝ] F, ‖S - T‖ < ε →
      ∃ e : Y ≃L[ℝ] LinearMap.range (P : F →ₗ[ℝ] F), ∀ y : Y, (e y : F) = P (S y)

/-- The fibre `det(PS)` of `DET(T, P, ε) = ⋃_{‖S−T‖<ε} {S} × det(PS)`. -/
abbrev LD (T : E →L[ℝ] F) (P : F →L[ℝ] F) (ε : ℝ) (S : Metric.ball T ε) : Type :=
  fredholmDet (P.comp (S : E →L[ℝ] F))

/-- The fibre `det(S)` of `DET(E, F) = ⋃_S {S} × det(S)` over a Fredholm `S` (the base is the
project's `FredholmOp E F = {S // S.IsFredholm}`, with the norm topology). -/
abbrev DETF (S : FredholmOp E F) : Type := fredholmDet (S : E →L[ℝ] F)

/-- `γ_(T,P,ε) : (S, h) ↦ (S, γ^P_S(h))`, from `DET(E, F)` over the ball to `DET(T, P, ε)`. -/
def gammaChart {T : E →L[ℝ] F} {P : F →L[ℝ] F} {ε : ℝ} (hc : IsDetChart T P ε) :
    {p : TotalSpace ℝ (DETF (E := E) (F := F)) // (p.proj : E →L[ℝ] F) ∈ Metric.ball T ε} →
      TotalSpace ℝ (LD T P ε) :=
  fun p => ⟨⟨p.1.proj.1, p.2⟩,
    gammaProj p.1.proj.2 (hc.2.2.2.1 _ (mem_ball_iff_norm.mp p.2)) p.1.2⟩

/-- `DET(E, F)` and the charts: every Fredholm `T` admits `(T, P, ε)`, and every
`γ_(T,P,ε) : DET(E, F)|ball → DET(T, P, ε)` is a fibrewise linear bijection. -/
def B : Prop :=
  ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F],
    (∀ T : E →L[ℝ] F, T.IsFredholm → ∃ (P : F →L[ℝ] F) (ε : ℝ), IsDetChart T P ε) ∧
    ∀ (T : E →L[ℝ] F) (P : F →L[ℝ] F) (ε : ℝ) (hc : IsDetChart T P ε),
      Function.Bijective (gammaChart hc)

end

end RoundTrip.V6_24
