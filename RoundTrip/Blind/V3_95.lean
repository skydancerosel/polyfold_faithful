import Polyfold
/-! Blind formalization of V3_95 (the text's §3.1, Theorems 3.23 and 3.19, pp. 77, 74).  `B` is
the conjunction of the two claims.  Choices:
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the fibrewise
  linear structure as instances on `P ⁻¹' {x}`, `Bd : StrongBundle PX P`.
- "tame strong bundle": `IsTameStrongBundle` (defined here): tame base (`MPolyfold.IsTame`) and an
  equivalent strong bundle atlas all of whose charts have a tame base retraction
  (`ScRetraction.IsTame`).  A property of the given structure, not "every chart is tame".
- "sc-Fredholm section of a tame strong bundle": `StrongBundle.IsScFredholmSectionTame`
  (Definition 3.14 with the germ data of Definition 3.11 in a tame strong bundle chart, as the
  text recalls it for tame strong bundles, Definitions 3.50/3.51).
- The quoted (3.19) gives no setting of its own; I read it in the same setting as (3.23): an
  sc-Fredholm section of a tame strong bundle and a zero `x₀`, plus `d_X ≡ 0`
  (`MPolyfold.IsWithoutBoundary`: `d_X(x) = 0` for all `x`) and `f'(x₀)` onto
  (`StrongBundle.IsLinSurjAt`: in some strong bundle chart, `D(f̂ ∘ r)(z)|_{T_zO}` maps onto `K_z`).
- `S(f, U) = {y ∈ U | f(y) = 0}`; "there is an open `U ∋ x`" is an existential over open sets of
  `X` containing `x` (also for (3.19), where the text writes `S(f, U)` for such a `U`).
- (3.23) hypothesis "`f'(x)` onto and kernel in good position to `C_xX`" (`IsSurjGoodPosAt`,
  defined here), in *some* tame strong bundle chart around `x`: with `z = φ(x)` lifted to
  `z₁ ∈ E₁`, `T_zO = range Dr(z)`, `L = D(f̂ ∘ r)(z)`: `L` maps `T_zO` onto `K_z = {k | (z,k) ∈ K}`,
  and `ker L ∩ T_zO` is in good position (Definition 3.21 inside `T_zO`, with the text's
  sc-complement, `IsInGoodPositionSc`) to the partial cone `C_zO = T_zO ∩ C_z` (Definition 2.27).
  The project's `IsInGoodPositionIn` (algebraic complement) was not used.
- (3.23) conclusion: `S(f, U) ⊆ X_∞` ("consists of smooth points", `smoothSet`), a sub-M-polyfold
  (Definition 2.20; `S(f, U)` paracompact, needed for `subPolyfold`, asserted as part of the claim)
  whose induced structure is tame (`MPolyfold.IsTame`) and has a compatible manifold structure with
  boundary with corners (`HasCornerStructure`, Definition 4.1), and this structure is "uniquely
  determined": any two corner atlases equivalent to the induced structure are equivalent to each
  other (`CornerStructureUnique`, defined here).  This is my reading of "uniquely determined"
  (determined by the induced M-polyfold structure).
- (3.19) conclusion "`S(f, U)` is a smooth manifold": a sub-M-polyfold whose induced structure has
  an equivalent atlas of charts onto open subsets of finite-dimensional spaces with the constant
  sc-structure (`HasBoundarylessManifoldStructure`, defined here: corner charts with `C` the whole
  space), i.e. a smooth manifold without boundary.
- Nothing in the statement looks false to me.
-/
namespace RoundTrip.V3_95
open Polyfold

/-- Definition 3.21 inside the subspace `T`, with an sc-complement: `N ⊆ T`, `N ∩ C` has nonempty
interior in `N`, and `N` has an sc-complement `P` in `T` (`T_m = N_m ⊕ P_m` on every level) such
that `n ∈ C ⟺ n + p ∈ C` for `n ∈ N`, `p ∈ P`, `|p|₀ ≤ ε|n|₀`. -/
def IsInGoodPositionSc (E : ScBanach) (T : Submodule ℝ (E.lvl 0)) (C : Set (E.lvl 0))
    (N : Submodule ℝ (E.lvl 0)) : Prop :=
  N ≤ T ∧ (interior (Subtype.val ⁻¹' C : Set N)).Nonempty ∧
    ∃ Pc : Submodule ℝ (E.lvl 0), Pc ≤ T ∧ E.IsScSubspace Pc ∧
      (∀ m, E.levelSub N m ⊓ E.levelSub Pc m = ⊥ ∧
        E.levelSub N m ⊔ E.levelSub Pc m = E.levelSub T m) ∧
      ∃ ε > 0, ∀ n ∈ N, ∀ p ∈ Pc, ‖p‖ ≤ ε * ‖n‖ → (n ∈ C ↔ n + p ∈ C)

/-- The M-polyfold `QZ` has an equivalent atlas of charts onto open subsets of finite-dimensional
spaces with the constant sc-structure: a compatible smooth manifold structure without boundary. -/
def HasBoundarylessManifoldStructure {Z : Type} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] (QZ : MPolyfold Z) : Prop :=
  ∃ A : MAtlas Z, A.Equiv QZ.atlas ∧ ∀ χ ∈ A.charts,
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℝ V) (_ : FiniteDimensional ℝ V)
      (U : Set V) (hU : IsRelOpenInQuadrant (ScBanach.const V) Set.univ U),
      χ.model = LocalModel.ofRelOpen hU

/-- The compatible manifold-with-corners structure of `QZ` is unique: any two atlases of corner
charts equivalent to the atlas of `QZ` are equivalent to each other. -/
def CornerStructureUnique {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (QZ : MPolyfold Z) : Prop :=
  ∀ A₁ A₂ : MAtlas Z, A₁.Equiv QZ.atlas → A₂.Equiv QZ.atlas →
    (∀ χ ∈ A₁.charts, χ.IsCornerChart) → (∀ χ ∈ A₂.charts, χ.IsCornerChart) → A₁.Equiv A₂

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- A **tame strong bundle**: tame base, and an equivalent strong bundle atlas of charts whose base
retractions are tame. -/
def IsTameStrongBundle (Bd : StrongBundle PX P) : Prop :=
  PX.IsTame ∧ ∃ A : StrongBundleAtlas PX P, A.Equiv Bd.atlas ∧
    ∀ c ∈ A.charts, (IsStrongBundleRetraction.baseRetraction c.relOpen c.isRetraction).IsTame

/-- `f'(x)` is surjective and its kernel is in good position to the partial cone `C_xX`, read in a
tame strong bundle chart around `x`. -/
def IsSurjGoodPosAt (Bd : StrongBundle PX P) (f : X → Y) (x : X) : Prop :=
  ∃ c : StrongBundleChart PX P, Bd.IsTameChart c ∧ x ∈ c.φ.source ∧
  ∃ z₁ : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z₁ = c.φ.toPartialEquiv x ∧
    (∀ k : c.F.lvl 0, (c.φ.toPartialEquiv x, k) ∈ c.K →
      ∃ v ∈ rangeS (scDeriv c.U (StrongRetr.r c.R) z₁),
        scDeriv c.U (c.principal f ∘ StrongRetr.r c.R) z₁ v = k) ∧
    ∃ (n : ℕ) (W : ScBanach) (Tp : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
      c.φ.model.C = (Tp.lvl 0) ⁻¹' quadrant n W 0 ∧
      IsInGoodPositionSc c.φ.model.E (rangeS (scDeriv c.U (StrongRetr.r c.R) z₁))
        ((rangeS (scDeriv c.U (StrongRetr.r c.R) z₁) : Set (c.φ.model.E.lvl 0)) ∩
          partialQuadrantAtWith Tp (c.φ.toPartialEquiv x))
        (LinearMap.ker
            (scDeriv c.U (c.principal f ∘ StrongRetr.r c.R) z₁ :
              c.φ.model.E.lvl 0 →ₗ[ℝ] c.F.lvl 0) ⊓
          rangeS (scDeriv c.U (StrongRetr.r c.R) z₁))

end

/-- Theorem 3.23 (near a zero in good position, `S(f, U)` is a tame sub-M-polyfold of smooth points
with a unique compatible manifold-with-corners structure) and Theorem 3.19 (for `d_X ≡ 0` and
`f'(x₀)` onto, `S(f, U)` is a smooth manifold). -/
def B : Prop :=
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → IsZeroAt P f x →
    IsSurjGoodPosAt Bd f x →
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        {y | y ∈ U ∧ IsZeroAt P f y} ⊆ PX.smoothSet ∧
        ∃ (hS : PX.IsSubMPolyfold {y | y ∈ U ∧ IsZeroAt P f y})
          (_ : ParacompactSpace {y | y ∈ U ∧ IsZeroAt P f y}),
          (PX.subPolyfold hS).IsTame ∧ (PX.subPolyfold hS).HasCornerStructure ∧
          CornerStructureUnique (PX.subPolyfold hS)) ∧
  (∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P) (f : X → Y) (x₀ : X),
    IsTameStrongBundle Bd → Bd.IsScFredholmSectionTame f → PX.IsWithoutBoundary →
    IsZeroAt P f x₀ → Bd.IsLinSurjAt f x₀ →
      ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
        ∃ (hS : PX.IsSubMPolyfold {y | y ∈ U ∧ IsZeroAt P f y})
          (_ : ParacompactSpace {y | y ∈ U ∧ IsZeroAt P f y}),
          HasBoundarylessManifoldStructure (PX.subPolyfold hS))

end RoundTrip.V3_95
