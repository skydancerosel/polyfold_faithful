import Polyfold
/-! Blind formalization of V1_21 (the text's §1.3, Definition 1.23, p. 14).

Text: let `C` be a partial quadrant in `E` and `T : E → ℝᵏ ⊕ W` an sc-isomorphism with
`T(C) = [0,∞)ᵏ ⊕ W`.  For `x ∈ C` with `T(x) = (a₁, …, a_k, w)` put `d_C(x) = #{i : a_i = 0}`.
"The map `d_C : C → ℕ₀` is the *degeneracy index*; points with `d_C = 0` are interior, with
`d_C = 1` boundary points, with `d_C ≥ 2` corners."

Choices:
- Setting: `E W : ScBanach` (levels in `Type`, forced by the project's `ScBanach`), `k : ℕ`,
  `ℝᵏ` with its constant sc-structure `ScBanach.const (Fin k → ℝ)` (checked with `#print`), and
  `C ⊆ E₀`.
- The definition is written out by me:
  * `Presentation E C`: `k`, `W`, an sc-isomorphism `T : E ≅ ℝᵏ ⊕ W` (the project's `ScIso`,
    checked: continuous linear equivalences on all levels, compatible with the inclusions) with
    `C = T₀⁻¹([0,∞)ᵏ × W₀)`, i.e. `T(C) = [0,∞)ᵏ ⊕ W` (equivalent, `T₀` being bijective).  `C` is a
    partial quadrant iff a presentation exists.
  * `degWith T x = #{i : (T₀ x)_i = 0}` (the count with a given `T`).
  * `degC E C x`: the count with a chosen presentation of `C` (`0` if `C` has none); the
    terminology `IsInteriorPt`, `IsBoundaryPt`, `IsCornerPt` is defined from it (on `C`).
- B: the text calls the result "the map `d_C : C → ℕ₀`", a function of `C` alone, while it is
  computed with an arbitrary `T`.  I state the definition as the claim that the count does not
  depend on that choice: for EVERY presentation `T` of `C` and every `x ∈ C`,
  `d_C(x) = #{i : (T₀ x)_i = 0}`.  This makes B the same content as the next result (Lemma 1.24,
  "`d_C` does not depend on `T`"); the alternative, reading `d_C` as a function of `(C, T)`, would
  make B a tautology about my own definitions.  Outside `C` the text does not define `d_C`, so B
  only speaks about `x ∈ C`.
- I did not use the project's `degIndex`/`degIndexWith`/`quadrant`, though `#print` shows
  `degIndex` is defined the same way (count with a chosen presentation, `0` if none).
- Nothing looks false to me.
-/
namespace RoundTrip.V1_21
open Polyfold

/-- A presentation of `C ⊆ E₀` as a partial quadrant: `T : E ≅ ℝᵏ ⊕ W` with
`T(C) = [0,∞)ᵏ ⊕ W`. -/
structure Presentation (E : ScBanach) (C : Set (E.lvl 0)) where
  /-- The number `k` of half-line coordinates. -/
  k : ℕ
  /-- The complementary sc-Banach space `W`. -/
  W : ScBanach
  /-- The sc-isomorphism `T : E → ℝᵏ ⊕ W`. -/
  T : ScIso E ((ScBanach.const (Fin k → ℝ)).prod W)
  /-- `C = T⁻¹([0,∞)ᵏ ⊕ W)`. -/
  eq : C = T.lvl 0 ⁻¹' {p | ∀ i, 0 ≤ p.1 i}

/-- `#{i : a_i = 0}` for `T(x) = (a₁, …, a_k, w)`. -/
noncomputable def degWith {E : ScBanach} {k : ℕ} {W : ScBanach}
    (T : ScIso E ((ScBanach.const (Fin k → ℝ)).prod W)) (x : E.lvl 0) : ℕ :=
  (Finset.univ.filter fun i : Fin k => (T.lvl 0 x).1 i = 0).card

/-- The degeneracy index `d_C(x)`, computed with a chosen presentation of `C` (`0` if `C` is not
a partial quadrant). -/
noncomputable def degC (E : ScBanach) (C : Set (E.lvl 0)) (x : E.lvl 0) : ℕ :=
  open Classical in
  if h : Nonempty (Presentation E C) then degWith h.some.T x else 0

/-- Interior points: `d_C(x) = 0`. -/
def IsInteriorPt (E : ScBanach) (C : Set (E.lvl 0)) (x : E.lvl 0) : Prop :=
  x ∈ C ∧ degC E C x = 0

/-- Boundary points: `d_C(x) = 1`. -/
def IsBoundaryPt (E : ScBanach) (C : Set (E.lvl 0)) (x : E.lvl 0) : Prop :=
  x ∈ C ∧ degC E C x = 1

/-- Corners: `d_C(x) ≥ 2`. -/
def IsCornerPt (E : ScBanach) (C : Set (E.lvl 0)) (x : E.lvl 0) : Prop :=
  x ∈ C ∧ 2 ≤ degC E C x

/-- The degeneracy index `d_C : C → ℕ₀` is given by `#{i : a_i = 0}` for every presentation
`T` of `C`. -/
def B : Prop :=
  ∀ (E : ScBanach) (C : Set (E.lvl 0)) (P : Presentation E C), ∀ x ∈ C,
    degC E C x = degWith P.T x

end RoundTrip.V1_21
