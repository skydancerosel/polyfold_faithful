import Polyfold
/-! Blind formalization of V2_47 (the text's §2.4, Corollary 2.41, p. 44).

Text: if `(O, C, E)` is a tame retract, every `x ∈ O` lies in precisely `d_O(x)` faces.

Choices:
- Setting as in my `RoundTrip/Blind/V2_46.lean`: `E : ScBanach` (levels in `Type`, forced by
  `ScBanach`), `C O ⊆ E₀`, `(O, C, E)` a tame sc-smooth retract (the project's `IsTameRetract`,
  Definition 2.34, checked with `#print`: the image of a retraction `r` with `r.IsTame`, tame for
  every presentation of `C`), `hO : IsScRetract E C O` the (redundant) retract proof needed to
  build the M-polyfold `O`, and `O` nonempty (otherwise there is no `x`).
- "Faces" and `d_O`: Definition 2.39 and Definition 2.22 for the retract `O` regarded as an
  M-polyfold: `MPolyfold.IsFace` and `MPolyfold.degIndex` (checked with `#print`: the closure of a
  connected component of `{d = 1}`; the minimum of `d_{C'}(φ(x))` over the compatible charts
  around `x`) of the project's `LocalModel.toMPolyfold` (checked: the M-polyfold on the subtype
  `↥O` with the single chart `id`), as in `RoundTrip/Blind/V2_37.lean`, `V2_42.lean`.
- "Lies in precisely `d_O(x)` faces": the set of faces containing `x` has `Set.encard` equal to
  `d_O(x)` (an infinite set has `encard = ⊤`, so it is not mistaken for a finite count).  This is
  the statement that `O` is face-structured; I spell it out rather than use the project's
  `IsFaceStructured` (which, checked with `#print`, is the same formula).
- Nothing looks false to me.
-/
namespace RoundTrip.V2_47
open Polyfold

/-- Corollary 2.41: every point `x` of a tame retract `O` lies in exactly `d_O(x)` faces of `O`. -/
def B : Prop :=
  ∀ (E : ScBanach) (C O : Set (E.lvl 0)) (hO : IsScRetract E C O) (hne : O.Nonempty),
    IsTameRetract E C O →
      ∀ x : O,
        {F : Set O | ((LocalModel.mk E C O hO).toMPolyfold hne).IsFace F ∧ x ∈ F}.encard =
          (((LocalModel.mk E C O hO).toMPolyfold hne).degIndex x : ℕ∞)

end RoundTrip.V2_47
