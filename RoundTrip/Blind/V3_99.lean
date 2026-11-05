import Polyfold
/-! Blind formalization of V3_99 (the text's §3.1, Theorem 3.19, p. 74, the claim on `U`).
Choices:
- Setting: `X Y : Type` (universe 0; nothing depends on the universe).  `PX : MPolyfold X`,
  `P : Y → X` with the fibrewise linear structure as instances on `P ⁻¹' {x}`, and
  `Bd : StrongBundle PX P` (Definition 2.51).
- Hypotheses: those of Theorem 3.19 (as in my blind file V3_68): `d_X ≡ 0`
  (`MPolyfold.IsWithoutBoundary`), `f` an sc-Fredholm section (`StrongBundle.IsScFredholmSection`,
  Definition 3.14; no tameness assumed), `f(x₀) = 0` (`IsZeroAt`), `f'(x₀)` surjective
  (`StrongBundle.IsLinSurjAt`: onto in some strong bundle chart; a hypothesis, so the weakest
  intrinsic reading).  Doubt: the project's docstring of `IsScFredholmSection` says the text states
  Definition 3.14 for tame strong bundles; if Theorem 3.19 presupposes tameness, `B` is stronger
  than the text.
- "`U` can be chosen": there is an open `U ∋ x₀`; `S(f, U) = {y ∈ U | f(y) = 0}` (`zeroSetIn`).
  To speak of `T_yS(f, U)` I assert (as Theorem 3.19 does) that `S(f, U)` is a sub-M-polyfold
  (Definition 2.20; paracompact, an instance argument of the induced structure `subPolyfold`,
  Proposition 2.21; asserted, it is true); `T_yS(f, U)` is its tangent space at `y`.
- `f'(y)` is read in a strong bundle chart `c` around `y` (`Bd.IsChart c`): with `z = φ(y)` lifted
  to `z₁ ∈ E₁`, `f'(y) = D(f̂ ∘ r)(z)|_{T_zO} : T_zO → K_z` (`T_zO = range Dr(z)`,
  `K_z = {k | (z, k) ∈ K}`).  Both conclusions are intrinsic, so they are asserted in *every* such
  chart (the strong reading).
- "`f'(y)` surjective": `LinSurjInChart` (as in V3_68).
- "`ker f'(y) = T_yS(f, U)`": `T_yS` is embedded in `T_yX` by the tangent map of the inclusion
  `S(f, U) → X` (sc-smooth for the induced structure; its sc-smoothness `hi` is a well-formedness
  hypothesis of this conjunct, and by proof irrelevance `tangentMap hi` does not depend on it); in
  every strong bundle chart around `y` whose base chart is a chart of `X` (`PX.IsChart c.φ`, needed
  for `tangentChartMap`), the vector parts of `Tφ(Ti(w))`, `w ∈ T_yS(f, U)`, are exactly
  `ker D(f̂ ∘ r)(z) ∩ T_zO` (`TangentEqKer`, as in V3_68).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_99
open Polyfold

/-- `S(f, U) = {y ∈ U | f(y) = 0}`. -/
def zeroSetIn {X Y : Type} (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (f : X → Y)
    (U : Set X) : Set X :=
  {y | y ∈ U ∧ IsZeroAt P f y}

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- In the strong bundle chart `c` around `y`, `f'(y) = D(f̂ ∘ r)(z)|_{T_zO}` maps `T_zO` onto the
fibre `K_z` (`z = φ(y)`, lifted to `z₁ ∈ E₁`). -/
def LinSurjInChart (c : StrongBundleChart PX P) (f : X → Y) (y : X) : Prop :=
  ∃ z₁ : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z₁ = c.φ.toPartialEquiv y ∧
    ∀ k : c.F.lvl 0, (c.φ.toPartialEquiv y, k) ∈ c.K →
      ∃ v ∈ rangeS (scDeriv c.U (StrongRetr.r c.R) z₁),
        scDeriv c.U (c.principal f ∘ StrongRetr.r c.R) z₁ v = k

/-- `T_yS = ker f'(y)`, read in the strong bundle chart `c` around `y` (whose base chart is a chart
of `X`): the vector parts of `Tφ(Ti(w))` for the tangent vectors `w` of the sub-M-polyfold `S` at
`y` (`i : S → X` the inclusion) are exactly the vectors of `ker D(f̂ ∘ r)(z) ∩ T_zO`. -/
def TangentEqKer {S : Set X} (hS : PX.IsSubMPolyfold S) [ParacompactSpace S]
    (hi : (PX.subPolyfold hS).IsScSmoothMap PX Subtype.val) (c : StrongBundleChart PX P)
    (hφ : PX.IsChart c.φ) (f : X → Y) (y : X) : Prop :=
  ∃ z₁ : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z₁ = c.φ.toPartialEquiv y ∧
    {h : c.φ.model.E.lvl 0 | ∃ w : (PX.subPolyfold hS).TangentSpace,
        ((PX.subPolyfold hS).tangentProj w).1.1 = y ∧
        (MPolyfold.tangentChartMap hφ (MPolyfold.tangentMap hi w)).2 = h} =
      ((LinearMap.ker (scDeriv c.U (c.principal f ∘ StrongRetr.r c.R) z₁ :
            c.φ.model.E.lvl 0 →ₗ[ℝ] c.F.lvl 0) ⊓
          rangeS (scDeriv c.U (StrongRetr.r c.R) z₁) : Submodule ℝ (c.φ.model.E.lvl 0)) :
        Set (c.φ.model.E.lvl 0))

end

/-- Theorem 3.19 (`d_X ≡ 0`, `f'(x₀)` onto at a zero `x₀`): `U ∋ x₀` can be chosen such that
`S(f, U)` is a sub-M-polyfold, `f'(y)` is onto and `ker f'(y) = T_yS(f, U)` for all
`y ∈ S(f, U)`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X),
    PX.IsWithoutBoundary → Bd.IsScFredholmSection f → IsZeroAt P f x₀ →
    Bd.IsLinSurjAt f x₀ →
      ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
        ∃ (hS : PX.IsSubMPolyfold (zeroSetIn P f U)) (_ : ParacompactSpace (zeroSetIn P f U)),
          (∀ y ∈ zeroSetIn P f U, ∀ c : StrongBundleChart PX P, Bd.IsChart c →
            y ∈ c.φ.source → LinSurjInChart c f y) ∧
          (∀ hi : (PX.subPolyfold hS).IsScSmoothMap PX Subtype.val,
            ∀ y ∈ zeroSetIn P f U, ∀ (c : StrongBundleChart PX P) (hφ : PX.IsChart c.φ),
              Bd.IsChart c → y ∈ c.φ.source → TangentEqKer hS hi c hφ f y)

end RoundTrip.V3_99
