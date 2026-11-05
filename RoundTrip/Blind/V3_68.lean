import Polyfold
/-! Blind formalization of V3_68 (the text's §3.1, Theorem 3.19, p. 74). `B` is the conjunction of
the claims.  Choices:
- Setting: `X Y : Type` (universe 0; nothing depends on the universe).  `PX : MPolyfold X`,
  `P : Y → X` with the fibrewise linear structure as instances on `P ⁻¹' {x}`, and
  `Bd : StrongBundle PX P` (Definition 2.51).
- Hypotheses exactly as quoted: `d_X ≡ 0` (`MPolyfold.IsWithoutBoundary`, Definition 2.25), `f`
  an sc-Fredholm section of a strong bundle, `f(x₀) = 0` (`IsZeroAt`).  The quote says "a strong
  bundle", not "a tame strong bundle", so tameness is *not* assumed and "sc-Fredholm section" is
  `StrongBundle.IsScFredholmSection` (Definition 3.14: sc-smooth, regularizing, an sc-Fredholm
  germ at every smooth point with the germ data in some compatible strong bundle chart).  Doubt:
  the project's docstring of `IsScFredholmSection` says the text states Definition 3.14 for a
  *tame* strong bundle; if Theorem 3.19 tacitly presupposes tameness, this `B` is stronger than
  the text (with `d_X ≡ 0` the difference should be immaterial).
- `f'(y) : T_yX → Y_y` has no intrinsic linear structure in the project, so it is read in a strong
  bundle chart `c` around `y` (compatible with the bundle structure, `StrongBundle.IsChart`): with
  `z = φ(y)` lifted to `z₁ ∈ E₁`, `r` the base retraction, `T_zO = range Dr(z)` (the image of
  `T_yX` under `Tφ`), `K_z = {k | (z, k) ∈ K}` (the image of `Y_y`), `f'(y)` is
  `L = D(f̂ ∘ r)(z)|_{T_zO}` (`f̂` the principal part).  Since these notions are intrinsic, the
  *conclusions* about `f'` are stated in *every* such chart (the strong reading); the hypothesis
  "`f'(x₀)` surjective" is `StrongBundle.IsLinSurjAt` (some chart, the weak reading).
- "`f'(x₀)` is sc-Fredholm" (`ChartLinScFredholm`, as in the earlier blind file V3_46): `T_zO` and
  `K_z` are sc-subspaces (`ScBanach.IsScSubspace`, induced structures `ofSubspace`), `L` maps
  `T_zO` into `K_z`, is an sc-operator there and is sc-Fredholm (Definition 1.8, `IsScFredholm`),
  with index `scIndex` (`dim ker − dim coker`).
- `S(f, U) = {y ∈ U | f(y) = 0}` (`zeroSetIn`); "an open `U ∋ x₀`": an open set of `X`.
- "a sub-M-polyfold whose induced structure is that of a smooth manifold of dimension the
  Fredholm index": `IsSubMPolyfold` (Definition 2.20); `S(f, U)` paracompact (an instance
  argument of the induced structure `subPolyfold`, Proposition 2.21; asserted, it is true); the
  induced structure has an equivalent atlas of charts onto open subsets of `d`-dimensional spaces
  with the constant sc-structure (`HasManifoldStructureOfDim`, defined here; a smooth manifold
  *without boundary*, as `d_X ≡ 0`), where `d` is the index of the sc-Fredholm operator `f'(x₀)`
  (in every chart).
- "`f'(y)` is surjective at every `y ∈ S(f, U)`": `LinSurjInChart` in every chart around `y`
  (with the level-`1` lift `z₁` of `φ(y)` asserted to exist).
- "`ker f'(y) = T_yS(f, U)`": `T_yS(f, U)` is embedded in `T_yX` by the tangent map of the
  inclusion `S(f, U) → X` (an sc-smooth map from the induced structure, Proposition 2.21; its
  sc-smoothness `hi` is a well-formedness hypothesis of this conjunct, and by proof irrelevance
  `tangentMap hi` does not depend on `hi`).  In every strong bundle chart `c` around `y` whose base
  chart is a chart of `X` (`PX.IsChart c.φ`, needed for `tangentChartMap`), the vector parts of
  `Tφ(Ti(w))`, `w ∈ T_yS(f, U)` (`tangentProj w = y`), form exactly `ker L ∩ T_zO`
  (`TangentEqKer`).
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_68
open Polyfold

/-- The M-polyfold `QZ` has an equivalent atlas of charts onto open subsets of `d`-dimensional
spaces with the constant sc-structure: a compatible smooth `d`-manifold structure without
boundary. -/
def HasManifoldStructureOfDim {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (QZ : MPolyfold Z) (d : ℕ) : Prop :=
  ∃ A : MAtlas Z, A.Equiv QZ.atlas ∧ ∀ χ ∈ A.charts,
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℝ V) (_ : FiniteDimensional ℝ V)
      (U : Set V) (hU : IsRelOpenInQuadrant (ScBanach.const V) Set.univ U),
      Module.finrank ℝ V = d ∧ χ.model = LocalModel.ofRelOpen hU

/-- `S(f, U) = {y ∈ U | f(y) = 0}`. -/
def zeroSetIn {X Y : Type} (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (f : X → Y)
    (U : Set X) : Set X :=
  {y | y ∈ U ∧ IsZeroAt P f y}

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- In the strong bundle chart `c` around `x`, with `z = φ(x)` (lifted to `z₁ ∈ E₁`), the
linearization `D(f̂ ∘ r)(z)|_{T_zO} : T_zO → K_z` is an sc-Fredholm operator of index `i` between
the sc-subspaces `T_zO = Dr(z)E ⊆ E` and `K_z = {h | (z, h) ∈ K} ⊆ F` (induced sc-structures). -/
def ChartLinScFredholm (c : StrongBundleChart PX P) (f : X → Y) (x : X) (i : ℤ) : Prop :=
  ∃ z₁ : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z₁ = c.φ.toPartialEquiv x ∧
  ∃ Kz : Submodule ℝ (c.F.lvl 0),
    (Kz : Set (c.F.lvl 0)) = {h | (c.φ.toPartialEquiv x, h) ∈ c.K} ∧
  ∃ (hT : c.φ.model.E.IsScSubspace (rangeS (scDeriv c.U (StrongRetr.r c.R) z₁)))
    (hK : c.F.IsScSubspace Kz)
    (L₀ : ↥(c.φ.model.E.levelSub (rangeS (scDeriv c.U (StrongRetr.r c.R) z₁)) 0) →L[ℝ]
      ↥(c.F.levelSub Kz 0)),
    (∀ v, (L₀ v : c.F.lvl 0) =
      scDeriv c.U (c.principal f ∘ StrongRetr.r c.R) z₁ (v : c.φ.model.E.lvl 0)) ∧
    ∃ hL : @IsScOperator (c.φ.model.E.ofSubspace hT) (c.F.ofSubspace hK) L₀,
      IsScFredholm hL.toScOperator ∧ scIndex hL.toScOperator = i

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

/-- Theorem 3.19 (implicit function theorem, `d_X ≡ 0`): at a zero `x₀` of an sc-Fredholm section,
`f'(x₀)` is sc-Fredholm; if it is onto, then near `x₀` the zero set is a sub-M-polyfold which is a
smooth manifold of dimension the Fredholm index, `f'` is onto along it, and `ker f'(y) = T_yS`. -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X),
    PX.IsWithoutBoundary → Bd.IsScFredholmSection f → IsZeroAt P f x₀ →
      (∀ c : StrongBundleChart PX P, Bd.IsChart c → x₀ ∈ c.φ.source →
          ∃ i : ℤ, ChartLinScFredholm c f x₀ i) ∧
      (Bd.IsLinSurjAt f x₀ →
        ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
          ∃ (hS : PX.IsSubMPolyfold (zeroSetIn P f U)) (_ : ParacompactSpace (zeroSetIn P f U)),
            (∃ d : ℕ, HasManifoldStructureOfDim (PX.subPolyfold hS) d ∧
              ∀ c : StrongBundleChart PX P, Bd.IsChart c → x₀ ∈ c.φ.source →
                ChartLinScFredholm c f x₀ d) ∧
            (∀ y ∈ zeroSetIn P f U, ∀ c : StrongBundleChart PX P, Bd.IsChart c →
              y ∈ c.φ.source → LinSurjInChart c f y) ∧
            (∀ hi : (PX.subPolyfold hS).IsScSmoothMap PX Subtype.val,
              ∀ y ∈ zeroSetIn P f U, ∀ (c : StrongBundleChart PX P) (hφ : PX.IsChart c.φ),
                Bd.IsChart c → y ∈ c.φ.source → TangentEqKer hS hi c hφ f y))

end RoundTrip.V3_68
