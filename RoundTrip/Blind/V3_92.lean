import Polyfold
/-! Blind formalization of V3_92 (the text's §3.1, after Theorem 3.19, p. 75). Choices:
- Setting (Theorems 3.18/3.19, which the remark follows): `X Y : Type` (universe 0; nothing
  depends on the universe), `PX : MPolyfold X`, `P : Y → X` with the fibrewise linear structure as
  instances on `P ⁻¹' {x}`, `Bd : StrongBundle PX P` tame (`IsTameStrongBundle`, defined here as in
  the earlier blind files: tame base and an *equivalent* atlas of charts with tame base
  retractions), `f` an sc-Fredholm section (Definition 3.14, the project's
  `StrongBundle.IsScFredholmSection`), `s₁, …, sₙ ∈ Γ⁺(P)` (`StrongBundle.IsScPlusSection`), and
  `f(x₀) = 0` (`IsZeroAt`; "the linearization at `(0, x₀)`" is the linearization at a zero of
  `f̃`, which presupposes `f(x₀) = 0`).  These are the hypotheses the text clearly presupposes;
  the remark itself only uses that `f` is sc-smooth and the `sᵢ` are sc⁺.
- `f̃(r, x) = f(x) + Σᵢ rᵢ sᵢ(x)`: the section `paramSection f hf s hs` of the pull-back bundle
  `π*Y → ℝⁿ × X` (`π = Prod.snd`, `ℝⁿ × X` the product M-polyfold `(rnPolyfold n).prod PX`); the
  proofs `hf`, `hs` that `f`, `sᵢ` are sections are hypotheses (they follow from the others), and
  `ℝⁿ × X` paracompact is an instance hypothesis (needed to form the product; a true fact).
- Linearizations have no intrinsic form in the project, so they are read in charts, in the way
  the identification `T_{(0,x₀)}(ℝⁿ × X) = ℝⁿ ⊕ T_{x₀}X`, `(π*Y)_{(0,x₀)} = Y_{x₀}` is made: for
  *every* strong bundle chart `c` of `P` around `x₀` (`Bd.IsChart c`) and the product strong
  bundle chart `c̃` of `π*Y` pulled back from it at `r₀ = 0` (`PullbackChartData.ofProd c 0`,
  `toChart`; base chart `(r, x) ↦ (r, φ(x))` modelled on `ℝⁿ ⊕ E`, retraction `1 × r`, fibre `F`;
  the point of `π*Y` passed to `toChart` only fixes a junk value and is arbitrary).  With `z = φ(x₀)`
  lifted to `z₁ ∈ E₁`:
  `f̃'(0, x₀)` is `D(F̂ ∘ r̃)(0, z₁)` on `T_{(0,z)} = range Dr̃(0, z₁)` (`F̂` the principal part of `f̃`
  in `c̃`, `r̃` its base retraction); `f'(x₀)u` is `D(f̂ ∘ r)(z₁)u` (`f̂` the principal part of `f`
  in `c`); `eᵢ = sᵢ(x₀)` is its fibre coordinate `(Φ(sᵢ(x₀)))₂ ∈ F` in `c`.
  Claim: `D(F̂ ∘ r̃)(0, z₁)(h, u) = D(f̂ ∘ r)(z₁)u + Σᵢ hᵢ eᵢ` for every `(h, u) ∈ T_{(0,z)}`.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_92
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- A **tame strong bundle**: tame base, and an equivalent strong bundle atlas of charts whose base
retractions are tame. -/
def IsTameStrongBundle (Bd : StrongBundle PX P) : Prop :=
  PX.IsTame ∧ ∃ A : StrongBundleAtlas PX P, A.Equiv Bd.atlas ∧
    ∀ c ∈ A.charts, (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame

/-- The formula in the chart `c` of `P` and its product chart `c̃` of `π*Y` at `r₀ = 0`: at the
lift `(0, z₁)` of `(0, φ(x₀))`, the linearization of `f̃(r, x) = f(x) + Σ rᵢ sᵢ(x)` sends
`(h, u) ∈ T_{(0,z)}` to `D(f̂ ∘ r)(z₁)u + Σ hᵢ eᵢ`, `eᵢ = (Φ(sᵢ(x₀)))₂`. -/
def LinFormulaInChart (n : ℕ) [ParacompactSpace ((Fin n → ℝ) × X)]
    (c : StrongBundleChart PX P) (y : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))
    (f : X → Y) (s : Fin n → X → Y) (hf : IsSection P f) (hs : ∀ i, IsSection P (s i))
    (x₀ : X) (z₁ : c.φ.model.E.lvl 1) : Prop :=
  let c' := (PullbackChartData.ofProd (n := n) c 0).toChart y
  let w₁ : c'.φ.model.E.lvl 1 := ((0 : Fin n → ℝ), z₁)
  ∀ w ∈ rangeS (scDeriv c'.U (StrongRetr.r c'.R) w₁),
    scDeriv c'.U (c'.principal (paramSection f hf s hs) ∘ StrongRetr.r c'.R) w₁ w =
      scDeriv c.U (c.principal f ∘ StrongRetr.r c.R) z₁
          (w : (Fin n → ℝ) × c.φ.model.E.lvl 0).2 +
        ∑ i, (w : (Fin n → ℝ) × c.φ.model.E.lvl 0).1 i • (c.toPartialEquiv (s i x₀)).2

end

/-- The linearization of `f̃(r, x) = f(x) + Σ rᵢ sᵢ(x)` at `(0, x₀)` is
`(h, u) ↦ f'(x₀)u + Σ hᵢ eᵢ`, `eᵢ = sᵢ(x₀)` (read in every strong bundle chart of `P` around
`x₀` and its product chart of `π*Y`). -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (n : ℕ) [ParacompactSpace ((Fin n → ℝ) × X)]
    (f : X → Y) (s : Fin n → X → Y) (hf : IsSection P f) (hs : ∀ i, IsSection P (s i)) (x₀ : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSection f → (∀ i, Bd.IsScPlusSection (s i)) →
    IsZeroAt P f x₀ →
      ∀ (c : StrongBundleChart PX P), Bd.IsChart c → x₀ ∈ c.φ.source →
        ∀ (y : pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) (z₁ : c.φ.model.E.lvl 1),
          c.φ.model.E.toBase 1 z₁ = c.φ.toPartialEquiv x₀ →
            LinFormulaInChart n c y f s hf hs x₀ z₁

end RoundTrip.V3_92
