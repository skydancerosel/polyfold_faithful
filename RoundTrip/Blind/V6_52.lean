import Polyfold
/-! Blind formalization of V6_52 (the text's §6.5, the classes `[φ]`, their composition and the
category `PX`, pp. 227–228).

Text: for `t([φ]) = s([ψ])`, `[ψ] * [φ]` is the class of `γ`, equal to `φ(β(s))` on `[0, 1/2]`
and `ψ(β(s))` on `[1/2, 1]`; this gives a category `PX` whose objects are the smooth points of `X`
and whose morphisms `x → y` are the classes with source `x` and target `y`.

Choices:
- "This gives a category" is stated as the category axioms for the data described (B is their
  conjunction), not via Mathlib's `Category` class (whose existence would say nothing):
  (o) every smooth point carries the constant path (the identities are morphisms of `PX`; objects
  are the smooth points, and sc-smooth paths only join smooth points); (i) homotopy rel end points
  is an equivalence relation on the paths from `x` to `y` (the morphisms are classes); and, for
  the reparametrization `β`: (ii) the composite `γ` of `φ` (from `x` to `y`) and `ψ` (from `y` to
  `z`) exists as an sc-smooth path from `x` to `z`; (iii) its class depends only on `[φ]`, `[ψ]`;
  (iv) associativity up to homotopy; (v) the constant paths are two-sided identities up to
  homotopy.
- Setting: `X : Type` (universe 0, as asked), `PX : MPolyfold X`.  Paths as in
  `RoundTrip/Blind/V6_48.lean` (sc-smooth `γ : ℝ¹ → X`, only `[0, 1]` mattering); homotopy: the
  project's `ScHomotopic` (checked with `#print`, see V6_51).  The composite `γ` is any
  sc-smooth path equal to the formula on `[0, 1]` (its class does not depend on the values off
  `[0, 1]`).
- `β`: the quote does not restate it; it is the `β` of p. 228 (quoted in V6_49): `β : ℝ → ℝ`
  smooth with `β([0, 1/2]) = [0, 1]`, `β([1/2, 1]) = [1, 2]`, constant near `1/2`
  (`IsAdmissibleBetaB`, literally).  B is claimed for every such `β`.
- MISPRINT (formalized literally): `ψ(β(s))` on `[1/2, 1]` evaluates `ψ` on `[1, 2]`; at
  `s = 1/2` (`β = 1`) the two formulas give `φ(1) = y` and `ψ(1) = z`.  Evidently
  `ψ(β(s) − 1)`.  B uses the LITERAL formula (`IsConcatLitB`), and I believe the literal B is
  FALSE ((ii) fails as soon as `y ≠ z`).  `BIntended` (not the item, only an aid) uses
  `ψ(β(s) − 1)` and adds `β(0) = 0`, `β(1) = 2`.
- Nothing else looks false to me.
-/
namespace RoundTrip.V6_52
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- `γ` is an sc-smooth path (on `ℝ¹`) from `x` to `y`. -/
def IsPathB (PX : MPolyfold X) (γ : (Fin 1 → ℝ) → X) (x y : X) : Prop :=
  (rnPolyfold 1).IsScSmoothMap PX γ ∧ γ (pt1 0) = x ∧ γ (pt1 1) = y

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

/-- The category axioms of `PX` for a composition rule `conc φ ψ γ` ("`γ` represents
`[ψ] * [φ]`"): (o) identities exist at smooth points, (i) the classes, (ii) composites exist,
(iii) composition is well defined on classes, (iv) associativity, (v) identity laws. -/
def CatAxiomsB (PX : MPolyfold X) (conc : ((Fin 1 → ℝ) → X) → ((Fin 1 → ℝ) → X) →
    ((Fin 1 → ℝ) → X) → Prop) : Prop :=
  -- (o)
  (∀ x ∈ PX.smoothSet, IsPathB PX (fun _ => x) x x) ∧
  -- (i)
  (∀ x y : X, Equivalence (fun γ γ' : {γ : (Fin 1 → ℝ) → X // IsPathB PX γ x y} =>
    ScHomotopic PX γ.1 γ'.1)) ∧
  -- (ii)
  (∀ (φ ψ : (Fin 1 → ℝ) → X) (x y z : X), IsPathB PX φ x y → IsPathB PX ψ y z →
    ∃ γ : (Fin 1 → ℝ) → X, IsPathB PX γ x z ∧ conc φ ψ γ) ∧
  -- (iii)
  (∀ (φ φ' ψ ψ' γ γ' : (Fin 1 → ℝ) → X) (x y z : X),
    IsPathB PX φ x y → IsPathB PX φ' x y → IsPathB PX ψ y z → IsPathB PX ψ' y z →
    IsPathB PX γ x z → IsPathB PX γ' x z → ScHomotopic PX φ φ' → ScHomotopic PX ψ ψ' →
    conc φ ψ γ → conc φ' ψ' γ' → ScHomotopic PX γ γ') ∧
  -- (iv) `[χ] * ([ψ] * [φ]) = ([χ] * [ψ]) * [φ]`
  (∀ (φ ψ χ γ₁ γ₂ γ₃ γ₄ : (Fin 1 → ℝ) → X) (w x y z : X),
    IsPathB PX φ w x → IsPathB PX ψ x y → IsPathB PX χ y z →
    IsPathB PX γ₁ w y → conc φ ψ γ₁ → IsPathB PX γ₂ w z → conc γ₁ χ γ₂ →
    IsPathB PX γ₃ x z → conc ψ χ γ₃ → IsPathB PX γ₄ w z → conc φ γ₃ γ₄ →
    ScHomotopic PX γ₂ γ₄) ∧
  -- (v) `[c_y] * [φ] = [φ] = [φ] * [c_x]`
  (∀ (φ γ : (Fin 1 → ℝ) → X) (x y : X), IsPathB PX φ x y → IsPathB PX γ x y →
    (IsPathB PX (fun _ => x) x x → conc (fun _ => x) φ γ → ScHomotopic PX γ φ) ∧
    (IsPathB PX (fun _ => y) y y → conc φ (fun _ => y) γ → ScHomotopic PX γ φ))

end

/-- The composition `[ψ] * [φ] = [γ]` (literal formula of p. 228) makes the smooth points and the
classes of sc-smooth paths a category `PX`, for every reparametrization `β` as on p. 228. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    (β : ℝ → ℝ), IsAdmissibleBetaB β → CatAxiomsB PX (IsConcatLitB β)

/-- Not the item: B with the evident correction `ψ(β(s) − 1)` (and `β(0) = 0`, `β(1) = 2`). -/
def BIntended : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    (β : ℝ → ℝ), IsAdmissibleBetaIntB β → CatAxiomsB PX (IsConcatIntB β)

end RoundTrip.V6_52
