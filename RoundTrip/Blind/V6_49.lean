import Polyfold
/-! Blind formalization of V6_49 (the text's §6.5, the paths after Theorem 6.35, p. 227, the
concatenation, p. 228, and the recollection on p. 201).

Text: for `y ∈ U` one takes an sc-smooth path `φ : [0, 1] → U` from `x` to `y`.  The composition
of paths is `φ(β(s))` for `s ∈ [0, 1/2]` and `ψ(β(s))` for `s ∈ [1/2, 1]`, for a smooth `β` with
`β([0, 1/2]) = [0, 1]`, `β([1/2, 1]) = [1, 2]`, constant near `1/2`.  On p. 201 the text recalls
that an M-polyfold is locally path connected and that smooth points of one path component are
joined by an sc⁺-smooth path.

Choices:
- B is the conjunction of three claims: (a) the path exists, (b) the composition is an sc-smooth
  path (for some, and then any, such `β`), (c) the two facts recalled from p. 201.
- Setting: `X : Type` (universe 0, as asked), `PX : MPolyfold X`; for (a) the instance family
  `ParacompactSpace ((Fin n → ℝ) × X)` (needed only to form the product M-polyfold `ℝ¹ × X` in
  "sc-smoothly contractible"; a true fact, not a hypothesis of the text).  No strong bundle is
  needed for these claims.
- Paths: as in `RoundTrip/Blind/V6_48.lean`, an sc-smooth path is an sc-smooth `γ : ℝ¹ → X`
  (`ℝ¹ = Fin 1 → ℝ`, `rnPolyfold 1`), only `[0, 1]` mattering; "`φ : [0, 1] → U`" means
  `γ([0, 1]) ⊆ U`.  A map given by a formula on `[0, 1]` "is an sc-smooth path" if it is the
  restriction of such a `γ` (`∃ γ`, agreeing with the formula on `[0, 1]`).
- (a) "`U`" is the `U(x)` of Theorem 6.35: an open sc-smoothly contractible set containing the
  smooth point `x` (`IsScContractibleB`, as in V6_48: `H : ℝ¹ × U → X` sc-smooth,
  `H([0,1] × U) ⊆ U`, `H(0, ·) = id`, `H(1, ·)` constant).  I state (a) for every such `U` (the
  local propagation property plays no role in the existence of paths) and for every SMOOTH
  `y ∈ U` (the text works with `y ∈ U_∞`; sc-smooth paths only reach smooth points).
- (b) "smooth `β`": `β : ℝ → ℝ`, `C^∞` (a smooth function on `[0, 1]` extends to `ℝ`), with
  `β '' [0, 1/2] = [0, 1]`, `β '' [1/2, 1] = [1, 2]` and `β` constant on a neighbourhood of
  `1/2` (`IsAdmissibleBetaB`, literally these three properties).  "For a smooth `β`": such a `β`
  exists, and the claim is made for any such `β`.  "The composition of paths" of `φ` from `x` to
  `y` and `ψ` from `y` to `z` is an sc-smooth path from `x` to `z` equal to the formula on
  `[0, 1]`.
- MISPRINT (formalized literally): `ψ(β(s))` for `s ∈ [1/2, 1]` evaluates `ψ` on
  `β(s) ∈ [1, 2]`, outside its parameter interval; at `s = 1/2` (where `β = 1`) the two formulas
  give `φ(1) = y` and `ψ(1) = z`.  It is evidently `ψ(β(s) − 1)`.  B states it LITERALLY
  (`IsConcatLitB`), and I believe the literal B is FALSE (any `x`, `y ≠ z` joined by paths give a
  contradiction at `s = 1/2`).  `BIntended` (not the item, only an aid) uses `ψ(β(s) − 1)` and
  adds `β(0) = 0`, `β(1) = 2` (not implied by the image conditions, needed for the end points).
- (c) "locally path connected": Mathlib's `LocallyPathConnectedSpace X` (topology of `X = X₀`).
  "Smooth points of one path component": `x, y ∈ X_∞` with `y ∈ pathComponent x` (continuous
  paths).  "Sc⁺-smooth path": a path into the shifted M-polyfold `X¹` (the project's
  `PX.shift` on `PX.Level 1`, Definition after 2.14), i.e. an sc-smooth `γ¹ : ℝ¹ → X¹`, whose
  end points (read in `X` by the inclusion `levelVal`) are `x` and `y`.  (For paths from the
  finite-dimensional `ℝ¹`, I believe sc⁺-smooth and sc-smooth coincide.)
- Nothing else looks false to me.
-/
namespace RoundTrip.V6_49
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- `U` is sc-smoothly contractible (as in V6_48). -/
def IsScContractibleB (PX : MPolyfold X) [ParacompactSpace ((Fin 1 → ℝ) × X)] (U : Set X) :
    Prop :=
  ∃ H : (Fin 1 → ℝ) × X → X,
    ((rnPolyfold 1).prod PX).IsScSmoothOn PX H (Set.univ ×ˢ U) ∧
    (∀ q ∈ Set.Icc (0 : Fin 1 → ℝ) 1, ∀ u ∈ U, H (q, u) ∈ U) ∧
    (∀ u ∈ U, H (pt1 0, u) = u) ∧
    ∃ p ∈ U, ∀ u ∈ U, H (pt1 1, u) = p

/-- `γ` is an sc-smooth path (on `ℝ¹`) from `x` to `y`. -/
def IsPathB (PX : MPolyfold X) (γ : (Fin 1 → ℝ) → X) (x y : X) : Prop :=
  (rnPolyfold 1).IsScSmoothMap PX γ ∧ γ (pt1 0) = x ∧ γ (pt1 1) = y

/-- `γ([0, 1]) ⊆ U`. -/
def PathInB (γ : (Fin 1 → ℝ) → X) (U : Set X) : Prop :=
  ∀ q ∈ Set.Icc (0 : Fin 1 → ℝ) 1, γ q ∈ U

/-- The text's `β`: smooth, `β([0, 1/2]) = [0, 1]`, `β([1/2, 1]) = [1, 2]`, constant near `1/2`. -/
def IsAdmissibleBetaB (β : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) β ∧ β '' Set.Icc 0 (1 / 2) = Set.Icc 0 1 ∧
    β '' Set.Icc (1 / 2) 1 = Set.Icc 1 2 ∧ ∀ᶠ s in nhds (1 / 2 : ℝ), β s = β (1 / 2)

/-- Not used in B: `β` with also `β(0) = 0` and `β(1) = 2`. -/
def IsAdmissibleBetaIntB (β : ℝ → ℝ) : Prop :=
  IsAdmissibleBetaB β ∧ β 0 = 0 ∧ β 1 = 2

/-- LITERAL: `γ = φ ∘ β` on `[0, 1/2]` and `γ = ψ ∘ β` on `[1/2, 1]`. -/
def IsConcatLitB (β : ℝ → ℝ) (φ ψ γ : (Fin 1 → ℝ) → X) : Prop :=
  (∀ s ∈ Set.Icc (0 : ℝ) (1 / 2), γ (pt1 s) = φ (pt1 (β s))) ∧
    ∀ s ∈ Set.Icc (1 / 2 : ℝ) 1, γ (pt1 s) = ψ (pt1 (β s))

/-- Not used in B: `γ = φ ∘ β` on `[0, 1/2]` and `γ = ψ ∘ (β − 1)` on `[1/2, 1]`. -/
def IsConcatIntB (β : ℝ → ℝ) (φ ψ γ : (Fin 1 → ℝ) → X) : Prop :=
  (∀ s ∈ Set.Icc (0 : ℝ) (1 / 2), γ (pt1 s) = φ (pt1 (β s))) ∧
    ∀ s ∈ Set.Icc (1 / 2 : ℝ) 1, γ (pt1 s) = ψ (pt1 (β s - 1))

end

/-- (a) In an open sc-smoothly contractible `U ∋ x`, every smooth `y ∈ U` is reached by an
sc-smooth path in `U` from `x`. -/
def ClaimA : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)] (U : Set X) (x y : X),
    IsOpen U → IsScContractibleB PX U → x ∈ U → x ∈ PX.smoothSet → y ∈ U → y ∈ PX.smoothSet →
      ∃ γ : (Fin 1 → ℝ) → X, IsPathB PX γ x y ∧ PathInB γ U

/-- (b), LITERAL: a smooth `β` as described exists, and for every such `β` the composition of an
sc-smooth path from `x` to `y` and one from `y` to `z` (literal formula) is an sc-smooth path from
`x` to `z`. -/
def ClaimBLit : Prop :=
  (∃ β : ℝ → ℝ, IsAdmissibleBetaB β) ∧
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    (β : ℝ → ℝ), IsAdmissibleBetaB β →
    ∀ (φ ψ : (Fin 1 → ℝ) → X) (x y z : X), IsPathB PX φ x y → IsPathB PX ψ y z →
      ∃ γ : (Fin 1 → ℝ) → X, IsPathB PX γ x z ∧ IsConcatLitB β φ ψ γ

/-- (b), corrected (not the item). -/
def ClaimBInt : Prop :=
  (∃ β : ℝ → ℝ, IsAdmissibleBetaIntB β) ∧
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    (β : ℝ → ℝ), IsAdmissibleBetaIntB β →
    ∀ (φ ψ : (Fin 1 → ℝ) → X) (x y z : X), IsPathB PX φ x y → IsPathB PX ψ y z →
      ∃ γ : (Fin 1 → ℝ) → X, IsPathB PX γ x z ∧ IsConcatIntB β φ ψ γ

/-- (c) (p. 201): an M-polyfold is locally path connected, and two smooth points in one path
component are joined by an sc⁺-smooth path (an sc-smooth path into `X¹`). -/
def ClaimC : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X),
    LocallyPathConnectedSpace X ∧
    ∀ x ∈ PX.smoothSet, ∀ y ∈ PX.smoothSet, y ∈ pathComponent x →
      ∃ γ : (Fin 1 → ℝ) → PX.Level 1, (rnPolyfold 1).IsScSmoothMap PX.shift γ ∧
        PX.levelVal 1 (γ (pt1 0)) = x ∧ PX.levelVal 1 (γ (pt1 1)) = y

/-- Paths in `U(x)` from `x`, the composition of sc-smooth paths (literal formula), and local
(sc⁺-smooth) path connectivity of M-polyfolds. -/
def B : Prop := ClaimA ∧ ClaimBLit ∧ ClaimC

/-- Not the item: B with the evident correction `ψ(β(s) − 1)` (and `β(0) = 0`, `β(1) = 2`). -/
def BIntended : Prop := ClaimA ∧ ClaimBInt ∧ ClaimC

end RoundTrip.V6_49
