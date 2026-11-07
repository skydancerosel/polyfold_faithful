import Polyfold
/-! Blind formalization of V6_51 (the text's §6.5, the homotopy classes `[φ]`, pp. 227–228).

Text: `[φ]` is the sc-smooth homotopy class of `φ : [0, 1] → X` with the end points fixed, with
source `φ(0)` and target `φ(1)`; the composition of classes is defined through a
reparametrization `β`.

Choices:
- The item is mostly definitional.  The claims it makes (needed for the definitions to make
  sense) are, and B is their conjunction: (i) sc-smooth homotopy with end points fixed is an
  equivalence relation on the sc-smooth paths from `x` to `y` (so the classes `[φ]` exist);
  (ii) source and target of a class are well defined (homotopic paths have the same end points);
  (iii) the composition "defined through a reparametrization `β`" exists (some `β` is admissible,
  and for every admissible `β` the composite is an sc-smooth path from `x` to `z`) and is well
  defined on classes: independent of the representatives AND of the reparametrization `β`
  (the "reparametrization homotopies" of the title).
- Setting: `X : Type` (universe 0, as asked), `PX : MPolyfold X`, any `x, y, z : X` (sc-smooth
  paths only join smooth points, so this is the text's range).
- Paths as in `RoundTrip/Blind/V6_48.lean`: sc-smooth `γ : ℝ¹ → X` (`rnPolyfold 1`), only
  `[0, 1]` mattering, `γ(0) = x`, `γ(1) = y` (`IsPathB`).
- "Sc-smooth homotopy with the end points fixed": the project's `ScHomotopic` /
  `IsScHomotopyRel` (checked with `#print`: `Φ : ℝ² → X` sc-smooth, `Φ(0, t) = γ₀(t)`,
  `Φ(1, t) = γ₁(t)` for `t ∈ [0, 1]`, `Φ(τ, 0) = γ₀(0)`, `Φ(τ, 1) = γ₀(1)` for `τ ∈ [0, 1]`).
  This is my reading, so I use it.
- "The composition … through a reparametrization `β`": the quote gives no formula; I take the
  one of p. 228 (quoted in the items V6_49/V6_52) with the evident correction of its misprint:
  `γ(s) = φ(β(s))` on `[0, 1/2]` and `γ(s) = ψ(β(s) − 1)` on `[1/2, 1]` (the p. 228 text has
  `ψ(β(s))`, which evaluates `ψ` on `[1, 2]`; see V6_49), for `β : ℝ → ℝ` smooth with
  `β([0, 1/2]) = [0, 1]`, `β([1/2, 1]) = [1, 2]`, constant near `1/2`, and (for the end points)
  `β(0) = 0`, `β(1) = 2` (`IsAdmissibleBetaB`).  `γ` is any sc-smooth path agreeing with this
  formula on `[0, 1]` (`IsConcatB`).
- Nothing looks false to me.
-/
namespace RoundTrip.V6_51
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- `γ` is an sc-smooth path (on `ℝ¹`) from `x` to `y`. -/
def IsPathB (PX : MPolyfold X) (γ : (Fin 1 → ℝ) → X) (x y : X) : Prop :=
  (rnPolyfold 1).IsScSmoothMap PX γ ∧ γ (pt1 0) = x ∧ γ (pt1 1) = y

/-- The reparametrization `β` of the composition: smooth, `β(0) = 0`, `β(1) = 2`,
`β([0, 1/2]) = [0, 1]`, `β([1/2, 1]) = [1, 2]`, constant near `1/2`. -/
def IsAdmissibleBetaB (β : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) β ∧ β 0 = 0 ∧ β 1 = 2 ∧ β '' Set.Icc 0 (1 / 2) = Set.Icc 0 1 ∧
    β '' Set.Icc (1 / 2) 1 = Set.Icc 1 2 ∧ ∀ᶠ s in nhds (1 / 2 : ℝ), β s = β (1 / 2)

/-- `γ` is the composite of `φ` and `ψ` through `β` on `[0, 1]`: `φ ∘ β` on `[0, 1/2]`,
`ψ ∘ (β − 1)` on `[1/2, 1]`. -/
def IsConcatB (β : ℝ → ℝ) (φ ψ γ : (Fin 1 → ℝ) → X) : Prop :=
  (∀ s ∈ Set.Icc (0 : ℝ) (1 / 2), γ (pt1 s) = φ (pt1 (β s))) ∧
    ∀ s ∈ Set.Icc (1 / 2 : ℝ) 1, γ (pt1 s) = ψ (pt1 (β s - 1))

end

/-- Homotopy classes of sc-smooth paths: sc-smooth homotopy rel end points is an equivalence
relation, source and target are well defined, and the composition through a reparametrization `β`
exists and is independent of the representatives and of `β`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X),
    -- (i) the classes
    (∀ x y : X, Equivalence (fun γ γ' : {γ : (Fin 1 → ℝ) → X // IsPathB PX γ x y} =>
      ScHomotopic PX γ.1 γ'.1)) ∧
    -- (ii) source and target of a class
    (∀ (γ γ' : (Fin 1 → ℝ) → X) (x y : X), IsPathB PX γ x y →
      (rnPolyfold 1).IsScSmoothMap PX γ' → ScHomotopic PX γ γ' → IsPathB PX γ' x y) ∧
    -- (iii) the composition through `β`: it exists …
    (∃ β : ℝ → ℝ, IsAdmissibleBetaB β) ∧
    (∀ (β : ℝ → ℝ), IsAdmissibleBetaB β → ∀ (φ ψ : (Fin 1 → ℝ) → X) (x y z : X),
      IsPathB PX φ x y → IsPathB PX ψ y z →
        ∃ γ : (Fin 1 → ℝ) → X, IsPathB PX γ x z ∧ IsConcatB β φ ψ γ) ∧
    -- … and depends only on the classes, not on `β`
    (∀ (β β' : ℝ → ℝ), IsAdmissibleBetaB β → IsAdmissibleBetaB β' →
      ∀ (φ φ' ψ ψ' γ γ' : (Fin 1 → ℝ) → X) (x y z : X),
        IsPathB PX φ x y → IsPathB PX φ' x y → IsPathB PX ψ y z → IsPathB PX ψ' y z →
        IsPathB PX γ x z → IsPathB PX γ' x z →
        ScHomotopic PX φ φ' → ScHomotopic PX ψ ψ' →
        IsConcatB β φ ψ γ → IsConcatB β' φ' ψ' γ' → ScHomotopic PX γ γ')

end RoundTrip.V6_51
