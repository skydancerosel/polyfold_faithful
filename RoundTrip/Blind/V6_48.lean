import Polyfold
/-! Blind formalization of V6_48 (the text's §6.5, the homotopy argument, pp. 226–227, and
Theorem 6.35, p. 227).

Text: for a strong bundle over a tame `X` and a smooth `x` there is an open sc-smoothly
contractible `U(x)` such that along every sc-smooth path `φ : [0, 1] → U` there is a well-defined
propagation `o ↦ φ_*o` of orientations of `DET(f, φ(0))`, and `φ_{0*}o = φ_{1*}o` for two such
paths with the same end points.  The proof homotopes `φ₀` to `φ₁` in `U`, using that `U` is
sc-smoothly contractible.

Choices:
- Setting: `X Y : Type` (universe 0, as asked; nothing depends on it), `PX : MPolyfold X`,
  `P : Y → X` with the fibrewise linear structure as instances on the fibres,
  `Bd : StrongBundle PX P` (Definition 2.51), `PX.IsTame` (Definition 2.37: "tame `X`"), and
  `f` an sc-Fredholm section, `Bd.IsScFredholmSection f` (Definition 3.14; the text's `f` of
  `DET(f, ·)`, implicit in the quote).  The two families of instances
  `ParacompactSpace ((Fin n → ℝ) × X)`, `ParacompactSpace (pullbackSpace P Prod.snd)` are only
  there because the project's `HasLocalPropagation` / `IsPush` take them as arguments (the
  product `ℝⁿ × X` and the pulled back bundle as M-polyfolds); they are true facts
  (`ℝⁿ × X` is paracompact for paracompact Hausdorff `X`, and the pull-back is homeomorphic to
  `ℝⁿ × Y`), not hypotheses of the text.
- NOT added: the push-forward construction (pp. 222–224) uses sc⁺-sections of `ℝ × X → Y`
  (to make `f − s(·, t)` vanish along the path and to span cokernels); their existence is
  usually derived from sc-smooth bump functions (Chapter 5).  The quote does not state such a
  hypothesis, so B does not have it.  DOUBT: without it the existence of push-forwards may fail.
- "sc-smooth path `φ : [0, 1] → U`": a map `γ : ℝ¹ → X` (`ℝ¹ = Fin 1 → ℝ`, the M-polyfold
  `rnPolyfold 1`) sc-smooth on all of `ℝ¹`, with `γ([0, 1]) ⊆ U`; only `[0, 1]` matters.  (An
  sc-smooth path on the closed interval becomes one of these after a reparametrization flat at
  the end points, which does not change the end points, the image or the homotopy class.)
  End points of such paths are automatically smooth points.
- The propagation is read in a strong bundle chart: `DET(f, y)` and its orientations
  `Or_y^f` are those of Definition 6.27 in a chart point (the project's `ChartPoint.Or`,
  `chartPtOf`), and "the propagation `o ↦ φ_*o`" is a push-forward `e` of the construction of
  pp. 222–224 in that chart (the project's `IsPush`, checked with `#print`: global sc⁺-sections
  `S`, `s₁, …, s_k` of the pulled back bundle with `(f + S)(t, γ(t)) = 0` near `t ∈ [0, 1]`, a
  family of stabilized kernels along `γ`, and `e` its push).  I trust `IsPush` to be the text's
  push-forward; I did not re-derive it.
- "there is a well-defined propagation …, and `φ_{0*}o = φ_{1*}o` for two such paths with the same
  end points": the project's `HasLocalPropagation f hf c hc U` (checked with `#print`: `U` lies in
  the domain of `c`; along every sc-smooth path in `U` a push-forward exists; and any two
  push-forwards along two paths in `U` with the same end points are equal — this covers both
  "well-defined", i.e. independent of the choices, for one path, and the path independence).
  It is exactly my reading, so I use it.
- "there is … `U(x)`": `∃` a chart `c` of the strong bundle (compatible with the atlas,
  `Bd.IsChart`) and `U` open with `x ∈ U` (`U ⊆ dom c` is part of `HasLocalPropagation`).  The
  text does not say "for every chart", so I do not require it.
- "sc-smoothly contractible" (`IsScContractibleB`, defined here, no project notion in the
  vocabulary): there are `H : ℝ¹ × X → X`, sc-smooth on the open set `ℝ¹ × U` of the product
  M-polyfold `ℝ¹ × X` (`MPolyfold.prod`), with `H([0, 1] × U) ⊆ U`, `H(0, ·) = id` and
  `H(1, ·)` constant (`= p ∈ U`) on `U`.  (Equivalent to the version with `H` defined on
  `[0, 1] × U` only, by a flat reparametrization in `t`.)
- The second sentence ("the proof homotopes `φ₀` to `φ₁` in `U`, using that `U` is sc-smoothly
  contractible") is the homotopy argument of pp. 226–227 that the item covers; I state it as the
  second conjunct of B, as a claim about every sc-smoothly contractible open `U` (of any
  M-polyfold): any two sc-smooth paths in `U` with the same end points are sc-smoothly homotopic
  with end points fixed by a homotopy with values in `U` on `[0, 1]²`.  Homotopy: the project's
  `IsScHomotopyRel` (checked with `#print`: `Φ : ℝ² → X` sc-smooth, `Φ(0, t) = γ₀(t)`,
  `Φ(1, t) = γ₁(t)` for `t ∈ [0, 1]`, `Φ(τ, 0) = γ₀(0)`, `Φ(τ, 1) = γ₀(1)` for `τ ∈ [0, 1]`).
- Nothing looks false to me apart from the DOUBT above.
-/
namespace RoundTrip.V6_48
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]

/-- `U` is sc-smoothly contractible: an sc-smooth `H : ℝ¹ × U → X` with `H([0,1] × U) ⊆ U`,
`H(0, ·) = id` and `H(1, ·)` constant on `U`. -/
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

end

/-- Theorem 6.35 (local propagation): every smooth point `x` has an open sc-smoothly contractible
neighbourhood `U` (in a strong bundle chart) with the local propagation property; and (the homotopy
argument) two sc-smooth paths with the same end points in an sc-smoothly contractible open `U` are
sc-smoothly homotopic in `U` with end points fixed. -/
def B : Prop :=
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
      [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
      [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
      [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
      (Bd : StrongBundle PX P) (f : X → Y) (hf : Bd.IsScFredholmSection f),
      PX.IsTame → ∀ x ∈ PX.smoothSet,
        ∃ (c : StrongBundleChart PX P) (hc : Bd.IsChart c) (U : Set X),
          IsOpen U ∧ x ∈ U ∧ IsScContractibleB PX U ∧ HasLocalPropagation f hf c hc U) ∧
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
      [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)] (U : Set X),
      IsOpen U → IsScContractibleB PX U →
      ∀ (γ₀ γ₁ : (Fin 1 → ℝ) → X) (x₀ x₁ : X),
        IsPathB PX γ₀ x₀ x₁ → IsPathB PX γ₁ x₀ x₁ → PathInB γ₀ U → PathInB γ₁ U →
        ∃ Φ : (Fin 2 → ℝ) → X, IsScHomotopyRel PX γ₀ γ₁ Φ ∧
          ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, Φ (pt2 τ t) ∈ U)

end RoundTrip.V6_48
