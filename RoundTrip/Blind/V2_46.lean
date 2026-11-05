import Polyfold
/-! Blind formalization of V2_46 (the text's §2.4, Lemma 2.40, p. 43).

Text: for a tame retract `(O, C, E)`, the faces of `O` are the connected components of the sets
`f ∩ O`, `f` an extended face; the components of `f ∩ O` and `f' ∩ O` through `x` agree iff
`f = f'`.

Choices:
- Setting: `E : ScBanach` (levels in `Type`, forced by `ScBanach`), `C O ⊆ E₀` with `(O, C, E)` a
  tame sc-smooth retract, the project's `IsTameRetract E C O` (Definition 2.34, checked with
  `#print`: `O = r(U)` for an `ScRetraction` `r` with `r.IsTame`, i.e. for every presentation `T`
  of `C`, `d_C(r(x)) = d_C(x)` on `U` and, at every smooth `x ∈ O`, `Dr(x)E` has an sc-complement
  inside `E_x`).  `hO : IsScRetract E C O` is the (redundant) retract proof needed to build the
  M-polyfold `O`, and `O` is assumed nonempty (an empty `O` has no faces and no components, and
  the project's M-polyfold of a retract needs a point).
- "The faces of `O`": the text regards the retract `O` as an M-polyfold (as before Theorem 2.31)
  and a face is Definition 2.39 for it: the closure of a connected component of `{d_O = 1}`.  This
  is `MPolyfold.IsFace` (checked with `#print`: `F = closure (connectedComponentIn {d = 1} x)` for
  some `x` with `d(x) = 1`) of the project's `LocalModel.toMPolyfold` (checked: the M-polyfold on
  the subtype `↥O` with the single chart `id`), with `d_O` its `MPolyfold.degIndex` (Definition
  2.22, the minimum of `d_{C'}(φ(x))` over all compatible charts around `x`), as in
  `RoundTrip/Blind/V2_37.lean` and `V2_42.lean`.  Faces are subsets of `↥O`; B compares their
  images in `E₀` (`Subtype.val ''`) with subsets of `E₀`.  The closure is taken in `O` (the
  subtype topology), as the text's faces are subsets of the space `O`.
- "Extended face" (`IsExtFaceB`, my definition): for a presentation `T : E ≅ ℝⁿ ⊕ W` of `C`
  (`C = T⁻¹([0,∞)ⁿ ⊕ W)`), the coordinate hyperplane `f_i = {z | (Tz)_i = 0}`, `i < n`.  I allow
  every presentation: the extended faces do not depend on it (`f_i` is the linear span of the
  face `C ∩ f_i` of `C`, and the faces of `C`, the closures of the components of `{d_C = 1}`, are
  intrinsic), so the union over all presentations is the set for any one of them.  Whether the
  extended face is the hyperplane or its trace `C ∩ f_i` does not matter here: `O ⊆ C` gives the
  same `f ∩ O`, and distinct `i` give distinct sets either way.
- "The connected components of the sets `f ∩ O`": the sets `connectedComponentIn (f ∩ O) x` with
  `x ∈ f ∩ O` (Mathlib; the component in the subspace topology).  First claim: a subset `G` of
  `O` is a face iff it is such a component for some extended face `f`.
- Second claim: for extended faces `f, f'` and `x ∈ f ∩ f' ∩ O`, the components of `f ∩ O` and
  `f' ∩ O` through `x` are equal iff `f = f'` (as sets).
- Nothing looks false to me.
-/
namespace RoundTrip.V2_46
open Polyfold

/-- An extended face of the partial quadrant `C`: a coordinate hyperplane `{z | (Tz)_i = 0}` of
some presentation `T : E ≅ ℝⁿ ⊕ W` of `C`. -/
def IsExtFaceB (E : ScBanach) (C : Set (E.lvl 0)) (f : Set (E.lvl 0)) : Prop :=
  ∃ (n : ℕ) (W : ScBanach) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)),
    C = T.lvl 0 ⁻¹' quadrant n W 0 ∧ ∃ i : Fin n, f = {z | ((T.lvl 0) z).1 i = 0}

/-- Lemma 2.40: the faces of a tame retract `O` are the connected components of the sets
`f ∩ O`, `f` an extended face of `C`; and the components of `f ∩ O`, `f' ∩ O` through a common
point agree only if `f = f'`. -/
def B : Prop :=
  ∀ (E : ScBanach) (C O : Set (E.lvl 0)) (hO : IsScRetract E C O) (hne : O.Nonempty),
    IsTameRetract E C O →
      -- the faces of `O` are the components of the sets `f ∩ O`
      (∀ G : Set O, ((LocalModel.mk E C O hO).toMPolyfold hne).IsFace G ↔
        ∃ f : Set (E.lvl 0), IsExtFaceB E C f ∧
          ∃ x ∈ f ∩ O, Subtype.val '' G = connectedComponentIn (f ∩ O) x) ∧
      -- components through `x` agree iff `f = f'`
      (∀ f f' : Set (E.lvl 0), IsExtFaceB E C f → IsExtFaceB E C f' →
        ∀ x ∈ f ∩ f' ∩ O,
          (connectedComponentIn (f ∩ O) x = connectedComponentIn (f' ∩ O) x ↔ f = f'))

end RoundTrip.V2_46
